/**
 * server.js — Backend Flot Maximum · Node.js + Express + SQLite (sql.js)
 * Lance avec : node server.js
 * Port par défaut : 3001
 */

const express = require("express");
const cors    = require("cors");
const fs      = require("fs");
const path    = require("path");
const initSqlJs = require("sql.js");

const app  = express();
const PORT = process.env.PORT || 3001;
const DB_PATH = path.join(__dirname, "maxflow.db");

app.use(cors());
app.use(express.json());

// ─── Initialisation SQL.js + chargement/création de la base ─────────────────
let db;   // instance SQL.js Database

async function openDb() {
  const SQL = await initSqlJs();

  if (fs.existsSync(DB_PATH)) {
    const data = fs.readFileSync(DB_PATH);
    db = new SQL.Database(data);
    console.log("📂 Base SQLite chargée depuis", DB_PATH);
  } else {
    db = new SQL.Database();
    console.log("🆕 Nouvelle base SQLite créée");
  }

  // Création des tables si elles n'existent pas
  db.run(`
    CREATE TABLE IF NOT EXISTS graphs (
      id          INTEGER PRIMARY KEY AUTOINCREMENT,
      name        TEXT    NOT NULL DEFAULT 'Sans titre',
      source_node TEXT    NOT NULL DEFAULT 'α',
      sink_node   TEXT    NOT NULL DEFAULT 'ω',
      created_at  TEXT    NOT NULL DEFAULT (datetime('now')),
      updated_at  TEXT    NOT NULL DEFAULT (datetime('now'))
    )
  `);

  db.run(`
    CREATE TABLE IF NOT EXISTS nodes (
      id       INTEGER PRIMARY KEY AUTOINCREMENT,
      graph_id INTEGER NOT NULL REFERENCES graphs(id) ON DELETE CASCADE,
      label    TEXT    NOT NULL,
      pos_x    REAL    NOT NULL DEFAULT 100,
      pos_y    REAL    NOT NULL DEFAULT 100
    )
  `);

  db.run(`
    CREATE TABLE IF NOT EXISTS edges (
      id       INTEGER PRIMARY KEY AUTOINCREMENT,
      graph_id INTEGER NOT NULL REFERENCES graphs(id) ON DELETE CASCADE,
      u        TEXT    NOT NULL,
      v        TEXT    NOT NULL,
      capacity INTEGER NOT NULL CHECK(capacity > 0)
    )
  `);

  db.run(`
    CREATE TABLE IF NOT EXISTS results (
      id         INTEGER PRIMARY KEY AUTOINCREMENT,
      graph_id   INTEGER NOT NULL REFERENCES graphs(id) ON DELETE CASCADE,
      max_flow   INTEGER NOT NULL,
      steps_json TEXT    NOT NULL,
      flow_json  TEXT    NOT NULL,
      computed_at TEXT   NOT NULL DEFAULT (datetime('now'))
    )
  `);

  saveDb(); // flush initial
}

// ─── Persistance sur disque après chaque écriture ───────────────────────────
function saveDb() {
  const data = db.export();
  fs.writeFileSync(DB_PATH, Buffer.from(data));
}

// ─── Helpers requêtes ────────────────────────────────────────────────────────
function all(sql, params = []) {
  const stmt = db.prepare(sql);
  stmt.bind(params);
  const rows = [];
  while (stmt.step()) rows.push(stmt.getAsObject());
  stmt.free();
  return rows;
}

function get(sql, params = []) {
  const rows = all(sql, params);
  return rows[0] || null;
}

function run(sql, params = []) {
  db.run(sql, params);
  // Récupère le dernier rowid
  const row = get("SELECT last_insert_rowid() as id");
  return row ? row.id : null;
}

// ─── ALGORITHME Edmonds-Karp (côté serveur, identique au frontend) ───────────
function bfs(cap, n, source, sink, parent) {
  const vis = new Array(n).fill(false);
  const q = [source]; vis[source] = true;
  while (q.length) {
    const u = q.shift();
    for (let v = 0; v < n; v++) {
      if (!vis[v] && cap[u][v] > 0) {
        vis[v] = true; parent[v] = u;
        if (v === sink) return true;
        q.push(v);
      }
    }
  }
  return false;
}

function edmondsKarp(nodeLabels, edgesArr, srcLabel, sinkLabel) {
  const n = nodeLabels.length;
  const idxMap = Object.fromEntries(nodeLabels.map((l, i) => [l, i]));
  const src = idxMap[srcLabel], sink = idxMap[sinkLabel];
  if (src === undefined || sink === undefined) return null;

  const initCap = Array.from({ length: n }, () => new Array(n).fill(0));
  for (const [u, v, c] of edgesArr)
    if (idxMap[u] !== undefined && idxMap[v] !== undefined)
      initCap[idxMap[u]][idxMap[v]] = c;

  const cap = initCap.map(r => [...r]);
  const parent = new Array(n).fill(-1);
  let maxFlow = 0;
  const steps = [];
  const edgeResiduals = [edgesArr.map(([u, v]) => {
    const ui = idxMap[u], vi = idxMap[v];
    return (ui !== undefined && vi !== undefined) ? cap[ui][vi] : 0;
  })];

  const getEdgeResiduals = () => edgesArr.map(([u, v]) => {
    const ui = idxMap[u], vi = idxMap[v];
    return (ui !== undefined && vi !== undefined) ? cap[ui][vi] : 0;
  });

  while (bfs(cap, n, src, sink, parent)) {
    let pf = Infinity;
    const path = [];
    for (let v = sink; v !== src; v = parent[v]) {
      const u = parent[v]; path.unshift([u, v]);
      pf = Math.min(pf, cap[u][v]);
    }
    let bottleneckEdgeIdx = -1;
    for (const [u, v] of path) {
      if (cap[u][v] === pf) {
        const idx = edgesArr.findIndex(([eu, ev]) => idxMap[eu] === u && idxMap[ev] === v);
        if (idx >= 0) { bottleneckEdgeIdx = idx; break; }
      }
    }
    const pathEdgeIndices = new Set();
    for (const [u, v] of path) {
      const idx = edgesArr.findIndex(([eu, ev]) => idxMap[eu] === u && idxMap[ev] === v);
      if (idx >= 0) pathEdgeIndices.add(idx);
    }
    for (const [u, v] of path) { cap[u][v] -= pf; cap[v][u] += pf; }
    maxFlow += pf;
    const afterResiduals = getEdgeResiduals();
    steps.push({
      path: path.map(([u, v]) => `${nodeLabels[u]}→${nodeLabels[v]}`).join(" "),
      pathFlow: pf, totalFlow: maxFlow,
      pathNodes: path.map(([u, v]) => [u, v]),
      pathEdgeIndices: [...pathEdgeIndices],
      bottleneckEdgeIdx,
      residualsBefore: edgeResiduals[edgeResiduals.length - 1],
      residualsAfter: afterResiduals,
    });
    edgeResiduals.push(afterResiduals);
    parent.fill(-1);
  }

  const flow = Array.from({ length: n }, () => new Array(n).fill(0));
  for (let u = 0; u < n; u++)
    for (let v = 0; v < n; v++)
      if (initCap[u][v] > 0) flow[u][v] = initCap[u][v] - cap[u][v];

  return { maxFlow, steps, flow, idxMap, initCap, edgeResiduals };
}

// ─── ROUTES ──────────────────────────────────────────────────────────────────

// GET /api/graphs — liste tous les graphes
app.get("/api/graphs", (req, res) => {
  try {
    const graphs = all("SELECT * FROM graphs ORDER BY updated_at DESC");
    res.json({ ok: true, data: graphs });
  } catch (e) {
    res.status(500).json({ ok: false, error: e.message });
  }
});

// POST /api/graphs — créer un nouveau graphe
app.post("/api/graphs", (req, res) => {
  try {
    const { name = "Sans titre", source_node = "α", sink_node = "ω",
            nodes = [], edges = [], positions = {} } = req.body;

    const graphId = run(
      "INSERT INTO graphs (name, source_node, sink_node) VALUES (?, ?, ?)",
      [name, source_node, sink_node]
    );

    for (const label of nodes) {
      const p = positions[label] || { x: 100, y: 100 };
      run("INSERT INTO nodes (graph_id, label, pos_x, pos_y) VALUES (?, ?, ?, ?)",
          [graphId, label, p.x, p.y]);
    }
    for (const [u, v, c] of edges) {
      run("INSERT INTO edges (graph_id, u, v, capacity) VALUES (?, ?, ?, ?)",
          [graphId, u, v, c]);
    }

    saveDb();
    res.status(201).json({ ok: true, data: { id: graphId } });
  } catch (e) {
    res.status(500).json({ ok: false, error: e.message });
  }
});

// GET /api/graphs/:id — charger un graphe complet
app.get("/api/graphs/:id", (req, res) => {
  try {
    const id = parseInt(req.params.id);
    const graph = get("SELECT * FROM graphs WHERE id = ?", [id]);
    if (!graph) return res.status(404).json({ ok: false, error: "Graphe introuvable" });

    const nodes     = all("SELECT * FROM nodes WHERE graph_id = ? ORDER BY id", [id]);
    const edges     = all("SELECT * FROM edges WHERE graph_id = ? ORDER BY id", [id]);
    const lastResult = get(
      "SELECT * FROM results WHERE graph_id = ? ORDER BY computed_at DESC LIMIT 1", [id]
    );

    const positions = {};
    for (const n of nodes) positions[n.label] = { x: n.pos_x, y: n.pos_y };

    res.json({
      ok: true,
      data: {
        ...graph,
        nodes: nodes.map(n => n.label),
        edges: edges.map(e => [e.u, e.v, e.capacity]),
        positions,
        last_result: lastResult ? {
          max_flow:   lastResult.max_flow,
          steps:      JSON.parse(lastResult.steps_json),
          flow:       JSON.parse(lastResult.flow_json),
          computed_at: lastResult.computed_at,
        } : null,
      }
    });
  } catch (e) {
    res.status(500).json({ ok: false, error: e.message });
  }
});

// PUT /api/graphs/:id — mettre à jour nom/source/puits
app.put("/api/graphs/:id", (req, res) => {
  try {
    const id = parseInt(req.params.id);
    const { name, source_node, sink_node } = req.body;
    db.run(
      "UPDATE graphs SET name=?, source_node=?, sink_node=?, updated_at=datetime('now') WHERE id=?",
      [name, source_node, sink_node, id]
    );
    saveDb();
    res.json({ ok: true });
  } catch (e) {
    res.status(500).json({ ok: false, error: e.message });
  }
});

// DELETE /api/graphs/:id
app.delete("/api/graphs/:id", (req, res) => {
  try {
    const id = parseInt(req.params.id);
    db.run("DELETE FROM results WHERE graph_id = ?", [id]);
    db.run("DELETE FROM edges   WHERE graph_id = ?", [id]);
    db.run("DELETE FROM nodes   WHERE graph_id = ?", [id]);
    db.run("DELETE FROM graphs  WHERE id = ?",       [id]);
    saveDb();
    res.json({ ok: true });
  } catch (e) {
    res.status(500).json({ ok: false, error: e.message });
  }
});

// ── Nœuds ────────────────────────────────────────────────────────────────────

// POST /api/graphs/:id/nodes — ajouter un nœud
app.post("/api/graphs/:id/nodes", (req, res) => {
  try {
    const graphId = parseInt(req.params.id);
    const { label, x = 100, y = 100 } = req.body;
    if (!label) return res.status(400).json({ ok: false, error: "label requis" });
    const exists = get("SELECT id FROM nodes WHERE graph_id=? AND label=?", [graphId, label]);
    if (exists) return res.status(409).json({ ok: false, error: "Nœud déjà existant" });

    const nodeId = run(
      "INSERT INTO nodes (graph_id, label, pos_x, pos_y) VALUES (?, ?, ?, ?)",
      [graphId, label, x, y]
    );
    db.run("UPDATE graphs SET updated_at=datetime('now') WHERE id=?", [graphId]);
    saveDb();
    res.status(201).json({ ok: true, data: { id: nodeId } });
  } catch (e) {
    res.status(500).json({ ok: false, error: e.message });
  }
});

// DELETE /api/graphs/:id/nodes/:label
app.delete("/api/graphs/:id/nodes/:label", (req, res) => {
  try {
    const graphId = parseInt(req.params.id);
    const { label } = req.params;
    db.run("DELETE FROM nodes WHERE graph_id=? AND label=?", [graphId, label]);
    db.run("DELETE FROM edges WHERE graph_id=? AND (u=? OR v=?)", [graphId, label, label]);
    db.run("UPDATE graphs SET updated_at=datetime('now') WHERE id=?", [graphId]);
    saveDb();
    res.json({ ok: true });
  } catch (e) {
    res.status(500).json({ ok: false, error: e.message });
  }
});

// PUT /api/graphs/:id/nodes/:label/position — mettre à jour position
app.put("/api/graphs/:id/nodes/:label/position", (req, res) => {
  try {
    const graphId = parseInt(req.params.id);
    const { label } = req.params;
    const { x, y } = req.body;
    db.run("UPDATE nodes SET pos_x=?, pos_y=? WHERE graph_id=? AND label=?", [x, y, graphId, label]);
    saveDb();
    res.json({ ok: true });
  } catch (e) {
    res.status(500).json({ ok: false, error: e.message });
  }
});

// ── Arcs ─────────────────────────────────────────────────────────────────────

// POST /api/graphs/:id/edges — ajouter un arc
app.post("/api/graphs/:id/edges", (req, res) => {
  try {
    const graphId = parseInt(req.params.id);
    const { u, v, capacity } = req.body;
    if (!u || !v || !capacity) return res.status(400).json({ ok: false, error: "u, v, capacity requis" });
    if (u === v) return res.status(400).json({ ok: false, error: "u ≠ v" });
    const cap = parseInt(capacity);
    if (isNaN(cap) || cap <= 0) return res.status(400).json({ ok: false, error: "capacity > 0" });
    const exists = get("SELECT id FROM edges WHERE graph_id=? AND u=? AND v=?", [graphId, u, v]);
    if (exists) return res.status(409).json({ ok: false, error: "Arc déjà existant" });

    const edgeId = run(
      "INSERT INTO edges (graph_id, u, v, capacity) VALUES (?, ?, ?, ?)",
      [graphId, u, v, cap]
    );
    db.run("UPDATE graphs SET updated_at=datetime('now') WHERE id=?", [graphId]);
    saveDb();
    res.status(201).json({ ok: true, data: { id: edgeId } });
  } catch (e) {
    res.status(500).json({ ok: false, error: e.message });
  }
});

// PUT /api/graphs/:id/edges/:edgeId — modifier capacité
app.put("/api/graphs/:id/edges/:edgeId", (req, res) => {
  try {
    const graphId = parseInt(req.params.id);
    const edgeId  = parseInt(req.params.edgeId);
    const cap = parseInt(req.body.capacity);
    if (isNaN(cap) || cap <= 0) return res.status(400).json({ ok: false, error: "capacity > 0" });
    db.run("UPDATE edges SET capacity=? WHERE id=? AND graph_id=?", [cap, edgeId, graphId]);
    db.run("UPDATE graphs SET updated_at=datetime('now') WHERE id=?", [graphId]);
    saveDb();
    res.json({ ok: true });
  } catch (e) {
    res.status(500).json({ ok: false, error: e.message });
  }
});

// DELETE /api/graphs/:id/edges/:edgeId
app.delete("/api/graphs/:id/edges/:edgeId", (req, res) => {
  try {
    const graphId = parseInt(req.params.id);
    const edgeId  = parseInt(req.params.edgeId);
    db.run("DELETE FROM edges WHERE id=? AND graph_id=?", [edgeId, graphId]);
    db.run("UPDATE graphs SET updated_at=datetime('now') WHERE id=?", [graphId]);
    saveDb();
    res.json({ ok: true });
  } catch (e) {
    res.status(500).json({ ok: false, error: e.message });
  }
});

// ── Calcul ───────────────────────────────────────────────────────────────────

// POST /api/graphs/:id/compute — lancer Edmonds-Karp et sauvegarder le résultat
app.post("/api/graphs/:id/compute", (req, res) => {
  try {
    const graphId = parseInt(req.params.id);
    const graph   = get("SELECT * FROM graphs WHERE id=?", [graphId]);
    if (!graph) return res.status(404).json({ ok: false, error: "Graphe introuvable" });

    const nodeRows = all("SELECT label FROM nodes WHERE graph_id=? ORDER BY id", [graphId]);
    const edgeRows = all("SELECT u, v, capacity FROM edges WHERE graph_id=? ORDER BY id", [graphId]);

    const nodeLabels = nodeRows.map(r => r.label);
    const edgesArr   = edgeRows.map(r => [r.u, r.v, r.capacity]);

    const result = edmondsKarp(nodeLabels, edgesArr, graph.source_node, graph.sink_node);
    if (!result) return res.status(400).json({ ok: false, error: "Source ou puits invalide" });

    // Supprimer anciens résultats pour ce graphe
    db.run("DELETE FROM results WHERE graph_id=?", [graphId]);

    run(
      "INSERT INTO results (graph_id, max_flow, steps_json, flow_json) VALUES (?, ?, ?, ?)",
      [graphId, result.maxFlow, JSON.stringify(result.steps), JSON.stringify(result.flow)]
    );
    db.run("UPDATE graphs SET updated_at=datetime('now') WHERE id=?", [graphId]);
    saveDb();

    // Reconstituer pathEdgeIndices comme Set dans la réponse JSON
    const steps = result.steps.map(s => ({
      ...s,
      pathEdgeIndices: s.pathEdgeIndices,
    }));

    res.json({
      ok: true,
      data: {
        maxFlow:       result.maxFlow,
        steps,
        flow:          result.flow,
        idxMap:        result.idxMap,
        initCap:       result.initCap,
        edgeResiduals: result.edgeResiduals,
      }
    });
  } catch (e) {
    res.status(500).json({ ok: false, error: e.message });
  }
});

// GET /api/graphs/:id/result — récupérer le dernier résultat calculé
app.get("/api/graphs/:id/result", (req, res) => {
  try {
    const graphId = parseInt(req.params.id);
    const graph   = get("SELECT * FROM graphs WHERE id=?", [graphId]);
    if (!graph) return res.status(404).json({ ok: false, error: "Graphe introuvable" });

    const nodeRows = all("SELECT label FROM nodes WHERE graph_id=? ORDER BY id", [graphId]);
    const edgeRows = all("SELECT u, v, capacity FROM edges WHERE graph_id=? ORDER BY id", [graphId]);
    const row      = get("SELECT * FROM results WHERE graph_id=? ORDER BY computed_at DESC LIMIT 1", [graphId]);
    if (!row) return res.json({ ok: true, data: null });

    const nodeLabels = nodeRows.map(r => r.label);
    const edgesArr   = edgeRows.map(r => [r.u, r.v, r.capacity]);
    const steps      = JSON.parse(row.steps_json);
    const flow       = JSON.parse(row.flow_json);
    const idxMap     = Object.fromEntries(nodeLabels.map((l, i) => [l, i]));

    // Recalcul de initCap et edgeResiduals pour le tableau BFS
    const n = nodeLabels.length;
    const initCap = Array.from({ length: n }, () => new Array(n).fill(0));
    for (const [u, v, c] of edgesArr)
      if (idxMap[u] !== undefined && idxMap[v] !== undefined)
        initCap[idxMap[u]][idxMap[v]] = c;

    const cap = initCap.map(r => [...r]);
    const edgeResiduals = [edgesArr.map(([u, v]) => {
      const ui = idxMap[u], vi = idxMap[v];
      return (ui !== undefined && vi !== undefined) ? cap[ui][vi] : 0;
    })];
    for (const step of steps) {
      for (const [u, v] of step.pathNodes) {
        cap[u][v] -= step.pathFlow;
        cap[v][u] += step.pathFlow;
      }
      edgeResiduals.push(edgesArr.map(([ul, vl]) => {
        const ui = idxMap[ul], vi = idxMap[vl];
        return (ui !== undefined && vi !== undefined) ? cap[ui][vi] : 0;
      }));
    }

    res.json({
      ok: true,
      data: {
        maxFlow: row.max_flow,
        steps,
        flow,
        idxMap,
        initCap,
        edgeResiduals,
        computed_at: row.computed_at,
      }
    });
  } catch (e) {
    res.status(500).json({ ok: false, error: e.message });
  }
});

// ── Données par défaut ────────────────────────────────────────────────────────

// POST /api/default — créer et retourner le graphe par défaut
app.post("/api/default", (req, res) => {
  try {
    const DEFAULT_NODES = ["α","A","B","C","D","E","F","G","H","I","J","K","L","ω"];
    const DEFAULT_EDGES = [
      ["α","A",15],["α","B",10],["α","C",15],["α","D",15],
      ["A","E",7],["B","A",5],["B","F",5],["C","F",10],["C","G",7],["D","G",10],
      ["E","H",4],["E","F",5],["E","I",15],
      ["F","G",5],["F","I",15],["G","I",15],
      ["H","J",7],["H","I",7],
      ["I","J",10],["I","K",30],["I","L",4],
      ["J","ω",15],["K","ω",20],["L","ω",15],
    ];
    const DEFAULT_POS = {
      α:{x:68,y:255}, A:{x:210,y:90},  B:{x:210,y:210}, C:{x:210,y:320}, D:{x:210,y:420},
      E:{x:370,y:65},  F:{x:370,y:210}, G:{x:370,y:380},
      H:{x:530,y:88},  I:{x:530,y:240},
      J:{x:685,y:105}, K:{x:685,y:240}, L:{x:685,y:375}, ω:{x:810,y:240},
    };

    const graphId = run(
      "INSERT INTO graphs (name, source_node, sink_node) VALUES (?, ?, ?)",
      ["Réseau par défaut", "α", "ω"]
    );
    for (const label of DEFAULT_NODES) {
      const p = DEFAULT_POS[label] || { x: 100, y: 100 };
      run("INSERT INTO nodes (graph_id, label, pos_x, pos_y) VALUES (?, ?, ?, ?)",
          [graphId, label, p.x, p.y]);
    }
    for (const [u, v, c] of DEFAULT_EDGES)
      run("INSERT INTO edges (graph_id, u, v, capacity) VALUES (?, ?, ?, ?)", [graphId, u, v, c]);

    saveDb();
    res.status(201).json({ ok: true, data: { id: graphId } });
  } catch (e) {
    res.status(500).json({ ok: false, error: e.message });
  }
});

// GET /api/health
app.get("/api/health", (_, res) => res.json({ ok: true, message: "Flot Maximum API opérationnelle" }));

// ─── Démarrage ───────────────────────────────────────────────────────────────
openDb().then(() => {
  app.listen(PORT, () => {
    console.log(`\n🚀 Serveur démarré sur http://localhost:${PORT}`);
    console.log(`   GET  /api/health`);
    console.log(`   GET  /api/graphs`);
    console.log(`   POST /api/graphs`);
    console.log(`   GET  /api/graphs/:id`);
    console.log(`   POST /api/graphs/:id/compute`);
    console.log(`   POST /api/default\n`);
  });
}).catch(err => {
  console.error("Erreur initialisation DB:", err);
  process.exit(1);
});