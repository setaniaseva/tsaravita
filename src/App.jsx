import { useState, useEffect, useRef, useCallback } from "react";

// ─── Config API ──────────────────────────────────────────────────────────────
const API = "http://localhost:3001/api";

// ─── Palette (Mode Clair) ──────────────────────────────────────────────────
const C = {
  bg: "#f0f4f8", 
  panel: "#ffffff", 
  panel2: "#f8fafc",
  border: "#d1d9e6", 
  accent: "#1a73e8", 
  accentDim: "#e8f0fe",
  green: "#0d9488", 
  greenDim: "#ccfbf1",
  orange: "#f97316", 
  red: "#dc2626", 
  purple: "#7c3aed",
  text: "#1e293b", 
  muted: "#94a3b8", 
  mutedLight: "#64748b",
  arcBlue: "#2563eb", 
  arcRed: "#dc2626", 
  arcFull: "#dc2626",
  arcPath: "#f59e0b", 
  arcZero: "#2563eb", 
  arcCut: "#7c3aed",
  nodeSource: "#b45309", 
  nodeSink: "#b45309",
  nodeFill: "#ffffff", 
  nodeText: "#1e293b",
  nodeReached: "#fef3c7", 
  flowHighlight: "#0d9488",
  tblBlue: "#dbeafe", 
  tblRed: "#fecaca", 
  tblOrange: "#fed7aa",
  tblHeader: "#1a56db",
  hover: "#e8f0fe",
};

// ─── Données par défaut ───────────────────────────────────────────────────
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

// ─── Algorithme local ─────────────────────────────────────────────────────
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

function edmondsKarpLocal(nodes, edges, srcLabel, sinkLabel) {
  const n = nodes.length;
  const idxMap = Object.fromEntries(nodes.map((l, i) => [l, i]));
  const src = idxMap[srcLabel], sink = idxMap[sinkLabel];
  if (src === undefined || sink === undefined) return null;
  const initCap = Array.from({ length: n }, () => new Array(n).fill(0));
  for (const [u, v, c] of edges)
    if (idxMap[u] !== undefined && idxMap[v] !== undefined)
      initCap[idxMap[u]][idxMap[v]] = c;
  const cap = initCap.map(r => [...r]);
  const parent = new Array(n).fill(-1);
  let maxFlow = 0;
  const steps = [];
  const getRes = () => edges.map(([u, v]) => {
    const ui = idxMap[u], vi = idxMap[v];
    return (ui !== undefined && vi !== undefined) ? cap[ui][vi] : 0;
  });
  const edgeResiduals = [getRes()];
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
        const idx = edges.findIndex(([eu, ev]) => idxMap[eu] === u && idxMap[ev] === v);
        if (idx >= 0) { bottleneckEdgeIdx = idx; break; }
      }
    }
    const pathEdgeIndices = new Set();
    for (const [u, v] of path) {
      const idx = edges.findIndex(([eu, ev]) => idxMap[eu] === u && idxMap[ev] === v);
      if (idx >= 0) pathEdgeIndices.add(idx);
    }
    for (const [u, v] of path) { cap[u][v] -= pf; cap[v][u] += pf; }
    maxFlow += pf;
    const afterRes = getRes();
    steps.push({
      path: path.map(([u, v]) => `${nodes[u]}→${nodes[v]}`).join(" "),
      pathFlow: pf, totalFlow: maxFlow,
      pathNodes: path.map(([u, v]) => [u, v]),
      pathEdgeIndices,
      bottleneckEdgeIdx,
      residualsBefore: edgeResiduals[edgeResiduals.length - 1],
      residualsAfter: afterRes,
    });
    edgeResiduals.push(afterRes);
    parent.fill(-1);
  }
  const flow = Array.from({ length: n }, () => new Array(n).fill(0));
  for (let u = 0; u < n; u++)
    for (let v = 0; v < n; v++)
      if (initCap[u][v] > 0) flow[u][v] = initCap[u][v] - cap[u][v];
  return { maxFlow, steps, flow, idxMap, initCap, edgeResiduals };
}

// ─── isFlowComplete ──────────────────────────────────────────────────────
function isFlowComplete(flow, edges, idxMap, sourceNode, sinkNode, nodes) {
  if (!flow || !edges || !idxMap) return false;
  const n = nodes.length;
  const cap = Array.from({ length: n }, () => new Array(n).fill(0));
  for (const [u, v, c] of edges) {
    const ui = idxMap[u], vi = idxMap[v];
    if (ui !== undefined && vi !== undefined) {
      cap[ui][vi] = c - flow[ui][vi];
      cap[vi][ui] += flow[ui][vi];
    }
  }
  const src = idxMap[sourceNode];
  const visited = new Array(n).fill(false);
  const queue = [src]; visited[src] = true;
  while (queue.length > 0) {
    const u = queue.shift();
    if (u === idxMap[sinkNode]) return false;
    for (let v = 0; v < n; v++)
      if (!visited[v] && cap[u][v] > 0) { visited[v] = true; queue.push(v); }
  }
  return true;
}

// ─── computeMinCut ───────────────────────────────────────────────────────
function computeMinCut(flow, edges, idxMap, sourceNode, sinkNode, nodes) {
  if (!flow || !edges || !idxMap) return null;
  const n = nodes.length;
  const residual = Array.from({ length: n }, () => new Array(n).fill(0));
  for (const [u, v, c] of edges) {
    const ui = idxMap[u], vi = idxMap[v];
    if (ui !== undefined && vi !== undefined) {
      residual[ui][vi] += c - flow[ui][vi];
      residual[vi][ui] += flow[ui][vi];
    }
  }
  const src = idxMap[sourceNode];
  const reached = new Array(n).fill(false);
  const queue = [src]; reached[src] = true;
  while (queue.length > 0) {
    const u = queue.shift();
    for (let v = 0; v < n; v++)
      if (!reached[v] && residual[u][v] > 0) { reached[v] = true; queue.push(v); }
  }
  const cutEdges = [];
  let cutCapacity = 0;
  for (const [u, v, c] of edges) {
    const ui = idxMap[u], vi = idxMap[v];
    if (ui === undefined || vi === undefined) continue;
    if (reached[ui] && !reached[vi]) { cutEdges.push([u, v, c]); cutCapacity += c; }
  }
  return {
    cutEdges, cutCapacity, reached,
    reachedLabels: nodes.filter((_, i) => reached[i]),
    unreachedLabels: nodes.filter((_, i) => !reached[i]),
  };
}

// ─── Arrow SVG ──────────────────────────────────────────────────────────────
function Arrow({ x1, y1, x2, y2, color, label, r = 24, offset = 0, pathEdge = false, flowValue = 0, thick = false, onClick, isHighlighted }) {
  const dx = x2 - x1, dy = y2 - y1;
  const len = Math.sqrt(dx * dx + dy * dy) || 1;
  const ux = dx / len, uy = dy / len;
  const ox = -uy * offset, oy = ux * offset;
  const sx = x1 + ux * r + ox, sy = y1 + uy * r + oy;
  const ex = x2 - ux * (r + 7) + ox, ey = y2 - uy * (r + 7) + oy;
  const mx = (sx + ex) / 2, my = (sy + ey) / 2;
  const lx = mx - uy * 14 + ox, ly = my + ux * 14 + oy;
  const mid = `m${color.replace(/[^a-z0-9]/gi, "")}${Math.round(x1)}${Math.round(y1)}${Math.round(x2)}`;
  const sw = thick ? 5 : (flowValue > 0 ? 3.5 : 2);
  const opacity = flowValue > 0 || thick ? 1 : 0.7;
  const finalColor = isHighlighted ? C.purple : color;
  
  return (
    <g style={{ cursor: 'pointer' }} onClick={onClick}>
      <defs>
        <marker id={mid} markerWidth="8" markerHeight="8" refX="4" refY="4" orient="auto">
          <path d="M0,1 L0,7 L7,4 z" fill={finalColor} />
        </marker>
      </defs>
      {(flowValue > 0 || thick) && (
        <line x1={sx} y1={sy} x2={ex} y2={ey} stroke={finalColor}
          strokeWidth={sw + 4} strokeOpacity={0.2} style={{ filter: "blur(4px)" }} />
      )}
      <line x1={sx} y1={sy} x2={ex} y2={ey} stroke={finalColor} strokeWidth={sw}
        markerEnd={`url(#${mid})`} strokeOpacity={opacity}
        strokeDasharray={pathEdge ? "6,3" : undefined} />
      {label !== undefined && (
        <text x={lx} y={ly} fill={finalColor} fontSize={flowValue > 0 ? "12" : "11"}
          fontWeight={flowValue > 0 ? "900" : "700"} textAnchor="middle" dominantBaseline="middle"
          style={{ filter: "drop-shadow(0 0 4px rgba(255,255,255,0.9))" }}>{label}</text>
      )}
    </g>
  );
}

// ─── GraphSVG avec clic sur noeuds ──────────────────────────────────────
function GraphSVG({ nodes, edges, pos, flow, result, highlightPath, sourceNode, sinkNode, showFlow, onNodeClick, selectedNode, onEdgeClick }) {
  const pathSet = new Set((highlightPath || []).map(([u, v]) => `${u}-${v}`));
  const idxMap = result?.idxMap || {};
  const edgeSet = new Set(edges.map(([u, v]) => `${u}-${v}`));
  
  // Trouver tous les chemins passant par le nœud sélectionné
  const getPathsThroughNode = (node) => {
    if (!result || !node || !selectedNode) return new Set();
    const paths = new Set();
    result.steps.forEach((step, idx) => {
      const pathNodes = step.pathNodes.flat();
      if (pathNodes.includes(result.idxMap[node])) {
        paths.add(idx);
      }
    });
    return paths;
  };

  const highlightedPaths = getPathsThroughNode(selectedNode);
  
  return (
    <svg viewBox="0 0 880 505" className="w-full rounded-2xl" style={{ background: "transparent" }}>
      <defs>
        <linearGradient id="bgGrad" x1="0%" y1="0%" x2="100%" y2="100%">
          <stop offset="0%" style={{ stopColor: "#f8fafc", stopOpacity: 1 }} />
          <stop offset="100%" style={{ stopColor: "#f0f4f8", stopOpacity: 1 }} />
        </linearGradient>
      </defs>
      <rect x="0" y="0" width="880" height="505" rx="16" fill="url(#bgGrad)" stroke="#d1d9e6" strokeWidth="1" />
      
      {edges.map(([ul, vl, cap], i) => {
        const ui = idxMap[ul], vi = idxMap[vl];
        const f = (flow && ui !== undefined && vi !== undefined) ? flow[ui][vi] : 0;
        const onPath = pathSet.has(`${ui}-${vi}`);
        const hasBidi = edgeSet.has(`${vl}-${ul}`);
        const off = hasBidi ? 8 : 0;
        
        // Vérifier si l'arc est dans un chemin passant par le nœud sélectionné
        const isHighlighted = selectedNode && result && 
          highlightedPaths.size > 0 && 
          result.steps.some((step, idx) => 
            highlightedPaths.has(idx) && 
            step.pathEdgeIndices.has(i)
          );
        
        let color;
        if (isHighlighted) color = C.purple;
        else if (onPath) color = C.arcPath;
        else if (showFlow && f > 0 && f === cap) color = C.arcFull;
        else if (showFlow && f > 0) color = C.flowHighlight;
        else color = C.arcBlue;
        
        const label = showFlow
          ? `${String(cap).padStart(2,"0")}(${String(f).padStart(2,"0")})`
          : `${String(cap).padStart(2,"0")}`;
        const p1 = pos[ul], p2 = pos[vl];
        if (!p1 || !p2) return null;
        
        return <Arrow key={i} x1={p1.x} y1={p1.y} x2={p2.x} y2={p2.y}
          color={color} label={label} offset={off} pathEdge={onPath} flowValue={f}
          onClick={() => onEdgeClick && onEdgeClick(ul, vl, cap, f)}
          isHighlighted={isHighlighted} />;
      })}
      
      {nodes.map(n => {
        const p = pos[n]; if (!p) return null;
        const special = n === sourceNode || n === sinkNode;
        const isSelected = selectedNode === n;
        
        return (
          <g key={n} style={{ cursor: 'pointer' }} onClick={() => onNodeClick && onNodeClick(n)}>
            {special && <circle cx={p.x} cy={p.y} r={30} fill="none" stroke={C.nodeSource} strokeWidth={2} strokeOpacity={0.4} />}
            {isSelected && (
              <circle cx={p.x} cy={p.y} r={28} fill="none" stroke={C.purple} strokeWidth={3} strokeOpacity={0.8} />
            )}
            <circle cx={p.x} cy={p.y} r={22} 
              fill={special ? C.nodeSource : (isSelected ? C.accentDim : C.nodeFill)} 
              stroke={isSelected ? C.purple : (special ? "#b45309" : "#94a3b8")} 
              strokeWidth={isSelected ? 3.5 : 2.5} />
            <text x={p.x} y={p.y} fill={C.nodeText} fontSize={n.length > 1 ? "11" : "13"} 
              fontWeight="900" textAnchor="middle" dominantBaseline="middle">{n}</text>
          </g>
        );
      })}
    </svg>
  );
}

// ─── Panneau de résultats détaillés pour un nœud ──────────────────────────
function NodeDetailsPanel({ node, result, nodes, edges, sourceNode, sinkNode, onClose }) {
  if (!node || !result) return null;

  const idxMap = result.idxMap;
  const nodeIdx = idxMap[node];
  if (nodeIdx === undefined) return null;

  // Trouver tous les chemins qui passent par ce nœud
  const pathsThroughNode = [];
  let totalFlowThroughNode = 0;

  result.steps.forEach((step, idx) => {
    const pathNodeIndices = step.pathNodes.flat();
    if (pathNodeIndices.includes(nodeIdx)) {
      pathsThroughNode.push({
        step: idx + 1,
        path: step.path,
        flow: step.pathFlow,
        total: step.totalFlow
      });
      totalFlowThroughNode += step.pathFlow;
    }
  });

  // Statistiques des arcs entrants et sortants
  const incomingEdges = edges.filter(([, v]) => v === node);
  const outgoingEdges = edges.filter(([u]) => u === node);
  
  const incomingFlow = incomingEdges.reduce((sum, [u, v]) => {
    const ui = idxMap[u], vi = idxMap[v];
    return sum + (ui !== undefined && vi !== undefined ? result.flow[ui][vi] : 0);
  }, 0);
  
  const outgoingFlow = outgoingEdges.reduce((sum, [u, v]) => {
    const ui = idxMap[u], vi = idxMap[v];
    return sum + (ui !== undefined && vi !== undefined ? result.flow[ui][vi] : 0);
  }, 0);

  const isSource = node === sourceNode;
  const isSink = node === sinkNode;

  return (
    <div className="p-5 rounded-2xl border" style={{background:C.panel, borderColor: C.purple, borderWidth: 2}}>
      <div className="flex items-center justify-between mb-4">
        <h3 className="text-xl font-black" style={{color: C.purple}}>
          📊 Résultats pour le nœud <span style={{color: C.nodeSource}}>{node}</span>
        </h3>
        <button onClick={onClose} className="text-xl" style={{color: C.muted}}>✕</button>
      </div>

      <div className="grid grid-cols-2 gap-3 mb-4">
        <div className="p-3 rounded-xl" style={{background: C.accentDim}}>
          <div className="text-xs" style={{color: C.muted}}>Flot entrant</div>
          <div className="text-2xl font-black" style={{color: C.arcBlue}}>{incomingFlow}</div>
        </div>
        <div className="p-3 rounded-xl" style={{background: C.accentDim}}>
          <div className="text-xs" style={{color: C.muted}}>Flot sortant</div>
          <div className="text-2xl font-black" style={{color: C.arcRed}}>{outgoingFlow}</div>
        </div>
      </div>

      {!isSource && !isSink && (
        <div className="mb-4 p-3 rounded-xl text-sm" style={{
          background: incomingFlow === outgoingFlow ? C.greenDim : C.tblRed,
          color: incomingFlow === outgoingFlow ? C.green : C.red
        }}>
          {incomingFlow === outgoingFlow 
            ? "✅ Conservation du flot vérifiée" 
            : "⚠️ Conservation du flot non vérifiée"}
        </div>
      )}

      {isSource && (
        <div className="mb-4 p-3 rounded-xl text-sm" style={{background: C.greenDim, color: C.green}}>
          🏷️ Nœud source - Débit total: {incomingFlow}
        </div>
      )}
      
      {isSink && (
        <div className="mb-4 p-3 rounded-xl text-sm" style={{background: C.greenDim, color: C.green}}>
          🏷️ Nœud puits - Débit total: {outgoingFlow}
        </div>
      )}

      {pathsThroughNode.length > 0 && (
        <div className="mb-4">
          <div className="font-bold text-sm mb-2" style={{color: C.accent}}>
            Chemins passant par {node} ({pathsThroughNode.length})
          </div>
          <div className="max-h-40 overflow-y-auto space-y-1">
            {pathsThroughNode.map((p, i) => (
              <div key={i} className="p-2 rounded-lg text-xs" style={{background: C.bg, borderLeft: `3px solid ${C.arcPath}`}}>
                <span style={{color: C.muted}}>Étape {p.step}:</span>
                <span className="font-mono" style={{color: C.text}}> {p.path}</span>
                <span style={{color: C.flowHighlight}}> +{p.flow}</span>
              </div>
            ))}
          </div>
          <div className="mt-2 text-sm font-bold" style={{color: C.purple}}>
            Total flot passant par {node}: {totalFlowThroughNode}
          </div>
        </div>
      )}

      {/* Liste des arcs incidents */}
      <div className="mb-4">
        <div className="font-bold text-sm mb-2" style={{color: C.accent}}>
          Arcs incidents
        </div>
        <div className="space-y-1">
          {incomingEdges.map(([u, v, cap], i) => {
            const ui = idxMap[u], vi = idxMap[v];
            const f = (ui !== undefined && vi !== undefined) ? result.flow[ui][vi] : 0;
            return (
              <div key={`in-${i}`} className="p-2 rounded-lg text-xs flex justify-between" style={{background: C.bg}}>
                <span><span style={{color: C.arcRed}}>{u}</span> → <span style={{color: C.arcBlue}}>{v}</span></span>
                <span style={{color: C.muted}}>{cap} → {f} ({f === cap ? 'saturé' : f > 0 ? 'partiel' : 'inactif'})</span>
              </div>
            );
          })}
          {outgoingEdges.map(([u, v, cap], i) => {
            const ui = idxMap[u], vi = idxMap[v];
            const f = (ui !== undefined && vi !== undefined) ? result.flow[ui][vi] : 0;
            return (
              <div key={`out-${i}`} className="p-2 rounded-lg text-xs flex justify-between" style={{background: C.bg}}>
                <span><span style={{color: C.arcRed}}>{u}</span> → <span style={{color: C.arcBlue}}>{v}</span></span>
                <span style={{color: C.muted}}>{cap} → {f} ({f === cap ? 'saturé' : f > 0 ? 'partiel' : 'inactif'})</span>
              </div>
            );
          })}
        </div>
      </div>

      <div className="text-xs" style={{color: C.muted}}>
        💡 Cliquez sur un autre nœud pour voir ses résultats
      </div>
    </div>
  );
}

// ─── BFS Tableau ─────────────────────────────────────────────────────────────
function BFSTableau({ result, edges, nodes, sourceNode, sinkNode }) {
  if (!result || !result.steps.length) return null;
  const { steps, initCap, idxMap, edgeResiduals } = result;

  const renderCell = (edgeIdx, stepIdx) => {
    const step = steps[stepIdx];
    const residualBefore = edgeResiduals[stepIdx][edgeIdx];
    const [u, v] = edges[edgeIdx];
    const ui = idxMap[u], vi = idxMap[v];
    const isOnPath = Array.isArray(step.pathEdgeIndices)
      ? step.pathEdgeIndices.includes(edgeIdx)
      : step.pathEdgeIndices?.has?.(edgeIdx);
    const isBottleneck = step.bottleneckEdgeIdx === edgeIdx;
    const residualAfter = edgeResiduals[stepIdx + 1]?.[edgeIdx] ?? 0;
    if (isBottleneck) return { val: residualBefore, bg: "#dc2626", color: "#fff", fw: "bold" };
    if (isOnPath) return { val: residualBefore, bg: "#2563eb", color: "#fff", fw: "bold" };
    if (residualAfter === 0 && (initCap[ui]?.[vi] ?? 0) > 0) return { val: "S", bg: "#f1f5f9", color: "#dc2626", fw: "bold" };
    if (residualBefore === 0) return { val: "S", bg: "#f1f5f9", color: "#dc2626", fw: "normal" };
    return { val: residualBefore, bg: C.tblBlue, color: "#1e293b", fw: "normal" };
  };

  const renderFinalCell = (edgeIdx) => {
    const residual = edgeResiduals[steps.length]?.[edgeIdx] ?? 0;
    const [u, v] = edges[edgeIdx];
    const ui = idxMap[u], vi = idxMap[v];
    const cap = (initCap[ui]?.[vi] ?? 0);
    if (residual === 0 && cap > 0) return { val: "S", bg: "#f1f5f9", color: "#dc2626", fw: "bold" };
    return { val: residual, bg: "#f8fafc", color: C.text, fw: "normal" };
  };

  return (
    <div>
      <div className="flex flex-wrap gap-4 mb-3 text-xs font-semibold">
        <span className="flex items-center gap-1.5">
          <span style={{ width:16,height:16,background:"#2563eb",borderRadius:3,display:"inline-block" }} />
          Arc sur le chemin augmentant
        </span>
        <span className="flex items-center gap-1.5">
          <span style={{ width:16,height:16,background:"#dc2626",borderRadius:3,display:"inline-block" }} />
          Goulot d'étranglement (Δ flot)
        </span>
        <span className="flex items-center gap-1.5">
          <span style={{ width:16,height:16,background:C.tblBlue,borderRadius:3,display:"inline-block" }} />
          Capacité résiduelle disponible
        </span>
        <span className="flex items-center gap-1.5">
          <span className="font-bold" style={{color:"#dc2626"}}>S</span>
          <span style={{color:C.muted}}> = Arc saturé (résidu = 0)</span>
        </span>
      </div>
      <div className="flex flex-wrap gap-2 mb-3">
        {steps.map((s, i) => (
          <div key={i} className="px-3 py-1.5 rounded-lg text-xs" style={{background:C.panel2,border:`1px solid ${C.border}`}}>
            <span style={{color:"#f59e0b",fontWeight:"bold"}}>Étape {i+1}</span>
            <span style={{color:C.muted}}> · +{s.pathFlow} · Total: </span>
            <span style={{color:C.green,fontWeight:"bold"}}>{s.totalFlow}</span>
          </div>
        ))}
      </div>
      <div className="overflow-x-auto rounded-xl border" style={{borderColor:C.border}}>
        <table style={{borderCollapse:"collapse",fontSize:11,minWidth:"100%"}}>
          <thead>
            <tr style={{background:"#1a56db"}}>
              <th style={{padding:"6px 8px",color:"#fff",fontWeight:"bold",border:`1px solid ${C.border}`,minWidth:36,position:"sticky",left:0,background:"#1a56db",zIndex:2}}>Arc</th>
              <th style={{padding:"6px 6px",color:"#fff",fontWeight:"bold",border:`1px solid ${C.border}`,minWidth:28,position:"sticky",left:46,background:"#1a56db",zIndex:2}}>Cap</th>
              {steps.map((_, si) => (
                <th key={si} style={{padding:"6px 6px",color:"#f59e0b",fontWeight:"bold",border:`1px solid ${C.border}`,minWidth:28,textAlign:"center"}}>{si+1}</th>
              ))}
              <th style={{padding:"6px 6px",color:"#0d9488",fontWeight:"bold",border:`1px solid ${C.border}`,minWidth:28}}>Fin</th>
            </tr>
            <tr style={{background:"#e8f0fe"}}>
              <td style={{padding:"3px 8px",color:C.muted,fontSize:9,border:`1px solid ${C.border}`,position:"sticky",left:0,background:"#e8f0fe",zIndex:2}}>u→v</td>
              <td style={{padding:"3px 6px",color:C.muted,fontSize:9,border:`1px solid ${C.border}`,position:"sticky",left:46,background:"#e8f0fe",zIndex:2}}>c</td>
              {steps.map((s, si) => (
                <td key={si} style={{padding:"3px 4px",color:"#f59e0b",fontSize:9,border:`1px solid ${C.border}`,textAlign:"center"}}>+{s.pathFlow}</td>
              ))}
              <td style={{padding:"3px 6px",color:C.muted,fontSize:9,border:`1px solid ${C.border}`}}></td>
            </tr>
          </thead>
          <tbody>
            {edges.map(([u, v, cap], edgeIdx) => (
              <tr key={edgeIdx} style={{borderBottom:`1px solid ${C.border}`}}>
                <td style={{padding:"4px 8px",fontWeight:"bold",color:"#1a56db",border:`1px solid ${C.border}`,whiteSpace:"nowrap",fontFamily:"monospace",position:"sticky",left:0,background:C.panel,zIndex:1}}>
                  {u}{v}
                </td>
                <td style={{padding:"4px 6px",fontWeight:"bold",color:C.text,border:`1px solid ${C.border}`,textAlign:"center",position:"sticky",left:46,background:C.panel,zIndex:1}}>
                  {cap}
                </td>
                {steps.map((_, si) => {
                  const cell = renderCell(edgeIdx, si);
                  return (
                    <td key={si} style={{padding:"4px 6px",background:cell.bg,color:cell.color,fontWeight:cell.fw,border:`1px solid ${C.border}`,textAlign:"center",fontFamily:"monospace",minWidth:28}}>
                      {cell.val}
                    </td>
                  );
                })}
                {(() => {
                  const fc = renderFinalCell(edgeIdx);
                  return (
                    <td style={{padding:"4px 6px",background:fc.bg,color:fc.color,fontWeight:fc.fw,border:`1px solid ${C.border}`,textAlign:"center",fontFamily:"monospace",minWidth:28}}>
                      {fc.val}
                    </td>
                  );
                })()}
              </tr>
            ))}
          </tbody>
        </table>
      </div>
      <div className="mt-3 text-xs" style={{color:C.muted}}>
        {steps.length} itération{steps.length>1?"s":""} BFS —
        <span style={{color:C.accent}}> Cellule bleue</span> = arc du chemin,
        <span style={{color:C.red}}> rouge</span> = goulot d'étranglement,
        <span style={{color:"#dc2626"}}> S</span> = saturé
      </div>
      <div className="mt-4 rounded-xl border overflow-hidden" style={{borderColor:C.border}}>
        <div className="px-4 py-2" style={{background:C.panel,borderBottom:`1px solid ${C.border}`}}>
          <span className="text-sm font-bold">Chemins augmentants BFS</span>
          <span className="ml-2 text-xs" style={{color:C.muted}}>({steps.length})</span>
        </div>
        <table className="w-full text-sm">
          <thead>
            <tr style={{background:C.bg}}>
              {["#","Chemin","Δ flot","Cumulé"].map(h => (
                <th key={h} className="px-4 py-2 text-left text-xs font-bold" style={{color:C.muted}}>{h}</th>
              ))}
            </tr>
          </thead>
          <tbody>
            {steps.map((s, i) => (
              <tr key={i} style={{borderBottom:`1px solid ${C.border}`}}>
                <td className="px-4 py-2 font-mono text-xs" style={{color:C.muted}}>{i+1}</td>
                <td className="px-4 py-2 font-mono text-xs" style={{color:C.text}}>
                  {sourceNode} → {s.path} → {sinkNode}
                </td>
                <td className="px-4 py-2 font-bold" style={{color:C.flowHighlight}}>+{s.pathFlow}</td>
                <td className="px-4 py-2 font-bold" style={{color:C.green}}>{s.totalFlow}</td>
              </tr>
            ))}
          </tbody>
        </table>
      </div>
    </div>
  );
}

// ─── Helpers UI ───────────────────────────────────────────────────────────────
function Field({ label, error, children }) {
  return (
    <div className="flex flex-col gap-1">
      <label className="text-xs font-semibold" style={{color:C.mutedLight}}>{label}</label>
      {children}
      {error && <span className="text-xs" style={{color:C.red}}>{error}</span>}
    </div>
  );
}

function Inp({ value, onChange, placeholder, type="text" }) {
  const [focus, setFocus] = useState(false);
  return (
    <input type={type} value={value} onChange={e=>onChange(e.target.value)} placeholder={placeholder}
      className="rounded-lg px-3 py-2 text-sm outline-none"
      style={{background:C.bg,color:C.text,border:`1.5px solid ${focus?C.accent:C.border}`}}
      onFocus={()=>setFocus(true)} onBlur={()=>setFocus(false)} />
  );
}

function Sel({ value, onChange, options }) {
  const [focus, setFocus] = useState(false);
  return (
    <select value={value} onChange={e=>onChange(e.target.value)}
      className="rounded-lg px-3 py-2 text-sm outline-none"
      style={{background:C.bg,color:C.text,border:`1.5px solid ${focus?C.accent:C.border}`}}
      onFocus={()=>setFocus(true)} onBlur={()=>setFocus(false)}>
      <option value="">— choisir —</option>
      {options.map(o => <option key={o} value={o}>{o}</option>)}
    </select>
  );
}

function Btn({ onClick, children, color=C.accent, textColor="#fff", sm, disabled }) {
  return (
    <button onClick={onClick} disabled={disabled}
      className={`rounded-xl font-bold transition-all active:scale-95 ${sm?"px-3 py-1.5 text-xs":"px-5 py-2.5 text-sm"} ${disabled?"opacity-40 cursor-not-allowed":""}`}
      style={{background:color,color:textColor}}>
      {children}
    </button>
  );
}

function TabBtn({ label, active, onClick }) {
  return (
    <button onClick={onClick} className="px-4 py-2.5 text-sm font-semibold rounded-xl transition-all"
      style={{background:active?C.accentDim:"transparent",color:active?C.accent:C.mutedLight,border:`1.5px solid ${active?C.accent:"transparent"}`}}>
      {label}
    </button>
  );
}

// ─── Panneau graphes sauvegardés ─────────────────────────────────────────────
function SavedGraphsPanel({ currentId, onLoad, onDelete, onNew, apiOk }) {
  const [graphs, setGraphs] = useState([]);

  const refresh = useCallback(async () => {
    if (!apiOk) return;
    try {
      const r = await fetch(`${API}/graphs`);
      const d = await r.json();
      if (d.ok) setGraphs(d.data);
    } catch {}
  }, [apiOk]);

  useEffect(() => { refresh(); }, [refresh, currentId]);

  const del = async (id, e) => {
    e.stopPropagation();
    if (!confirm("Supprimer ce graphe ?")) return;
    await fetch(`${API}/graphs/${id}`, { method: "DELETE" });
    refresh();
    if (id === currentId) onNew();
  };

  if (!apiOk) return (
    <div className="p-4 rounded-xl text-xs text-center" style={{background:C.panel2,color:C.muted}}>
      Attention: Backend non connecte — mode hors ligne
    </div>
  );

  return (
    <div>
      <div className="flex items-center justify-between mb-3">
        <span className="text-sm font-bold">Graphes sauvegardés</span>
        <button onClick={refresh} className="text-xs px-2 py-1 rounded-lg" style={{background:C.panel2,color:C.accent}}>↻</button>
      </div>
      {graphs.length === 0 && <div className="text-xs" style={{color:C.muted}}>Aucun graphe sauvegardé</div>}
      <div className="flex flex-col gap-2 max-h-64 overflow-y-auto">
        {graphs.map(g => (
          <div key={g.id} onClick={() => onLoad(g.id)}
            className="flex items-center justify-between px-3 py-2 rounded-xl cursor-pointer border transition-all"
            style={{background:g.id===currentId?C.accentDim:C.panel2,borderColor:g.id===currentId?C.accent:C.border}}>
            <div>
              <div className="text-sm font-semibold" style={{color:g.id===currentId?C.accent:C.text}}>{g.name}</div>
              <div className="text-xs" style={{color:C.muted}}>
                {g.source_node} → {g.sink_node} · {g.updated_at?.slice(0,16)}
              </div>
            </div>
            <button onClick={e=>del(g.id,e)} className="text-xs px-2 py-1 rounded-lg" style={{color:C.red}}>✕</button>
          </div>
        ))}
      </div>
    </div>
  );
}

// ─── Modal sauvegarde ─────────────────────────────────────────────────────────
function SaveModal({ onSave, onClose }) {
  const [name, setName] = useState("Mon graphe");
  return (
    <div className="fixed inset-0 z-50 flex items-center justify-center" style={{background:"rgba(0,0,0,0.5)"}}>
      <div className="rounded-2xl p-6 w-80 border" style={{background:C.panel,borderColor:C.border}}>
        <h3 className="font-bold mb-4" style={{color:C.accent}}>Sauvegarder le graphe</h3>
        <Field label="Nom du graphe">
          <Inp value={name} onChange={setName} placeholder="ex: Réseau principal" />
        </Field>
        <div className="flex gap-3 mt-4">
          <Btn onClick={()=>onSave(name)}>Sauvegarder</Btn>
          <Btn onClick={onClose} color={C.border} textColor={C.text}>Annuler</Btn>
        </div>
      </div>
    </div>
  );
}

// ─── CONFIG FORM ──────────────────────────────────────────────────────────────
function ConfigForm({ nodes, sourceNode, sinkNode, onApply }) {
  const [src, setSrc] = useState(sourceNode);
  const [snk, setSnk] = useState(sinkNode);
  useEffect(()=>{ setSrc(sourceNode); setSnk(sinkNode); }, [sourceNode,sinkNode]);
  return (
    <div className="rounded-2xl border p-5" style={{background:C.panel,borderColor:C.border}}>
      <h2 className="font-bold mb-4" style={{color:C.accent}}>Source & Puits</h2>
      <div className="flex flex-col gap-3">
        <Field label="Noeud source (α)"><Sel value={src} onChange={setSrc} options={nodes} /></Field>
        <Field label="Noeud puits (ω)"><Sel value={snk} onChange={setSnk} options={nodes} /></Field>
        <Btn onClick={()=>onApply(src,snk)}>Appliquer</Btn>
        <p className="text-xs p-3 rounded-xl" style={{background:C.bg,color:C.muted}}>
          Tout changement efface le résultat actuel.
        </p>
      </div>
    </div>
  );
}

// ─── APP ──────────────────────────────────────────────────────────────────────
export default function MaxFlowApp() {
  const [nodes, setNodes]           = useState([...DEFAULT_NODES]);
  const [edges, setEdges]           = useState(DEFAULT_EDGES.map(e=>[...e]));
  const [edgeIds, setEdgeIds]       = useState(DEFAULT_EDGES.map(()=>null));
  const [sourceNode, setSourceNode] = useState("α");
  const [sinkNode, setSinkNode]     = useState("ω");
  const [nodePos, setNodePos]       = useState({...DEFAULT_POS});
  const [currentGraphId, setCurrentGraphId] = useState(null);
  const [graphName, setGraphName]   = useState("");

  const [newNode, setNewNode]   = useState("");
  const [newEdge, setNewEdge]   = useState({from:"",to:"",cap:""});
  const [editEdge, setEditEdge] = useState(null);
  const [editCap, setEditCap]   = useState("");
  const [errors, setErrors]     = useState({});
  const [toast, setToast]       = useState(null);
  const [tab, setTab]           = useState("graph");

  const [result, setResult]           = useState(null);
  const [currentStep, setCurrentStep] = useState(-1);
  const [running, setRunning]         = useState(false);
  const [speed, setSpeed]             = useState(900);
  const [showFlow, setShowFlow]       = useState(false);
  const timerRef = useRef(null);

  const [apiOk, setApiOk]       = useState(false);
  const [apiLoading, setApiLoading] = useState(false);
  const [showSave, setShowSave] = useState(false);

  // État pour le nœud sélectionné
  const [selectedNode, setSelectedNode] = useState(null);

  const flowComplete = result && showFlow
    ? isFlowComplete(result.flow, edges, result.idxMap, sourceNode, sinkNode, nodes)
    : false;
  const minCut = result
    ? computeMinCut(result.flow, edges, result.idxMap, sourceNode, sinkNode, nodes)
    : null;

  // ── Vérification du backend ──
  useEffect(() => {
    fetch(`${API}/health`)
      .then(r=>r.json())
      .then(d=>{ if(d.ok) setApiOk(true); })
      .catch(()=>setApiOk(false));
  }, []);

  function toast_(msg, type="ok") {
    setToast({msg,type});
    setTimeout(()=>setToast(null), 2800);
  }

  // ── Charger un graphe depuis le backend ──────────────────────────────────
  async function loadGraph(id) {
    setApiLoading(true);
    try {
      const r = await fetch(`${API}/graphs/${id}`);
      const d = await r.json();
      if (!d.ok) throw new Error(d.error);
      const g = d.data;
      setNodes(g.nodes);
      setEdges(g.edges);
      setEdgeIds(g.edges.map(()=>null));
      setNodePos(g.positions);
      setSourceNode(g.source_node);
      setSinkNode(g.sink_node);
      setCurrentGraphId(id);
      setGraphName(g.name);
      setResult(null); setCurrentStep(-1); setShowFlow(false);
      setSelectedNode(null);

      if (g.last_result) {
        const res = g.last_result;
        const idxMap = Object.fromEntries(g.nodes.map((l,i)=>[l,i]));
        const n = g.nodes.length;
        const initCap = Array.from({length:n},()=>new Array(n).fill(0));
        for (const [u,v,c] of g.edges)
          if (idxMap[u]!==undefined && idxMap[v]!==undefined)
            initCap[idxMap[u]][idxMap[v]] = c;
        const cap2 = initCap.map(r=>[...r]);
        const edgeResiduals = [g.edges.map(([u,v])=>{
          const ui=idxMap[u],vi=idxMap[v];
          return (ui!==undefined&&vi!==undefined)?cap2[ui][vi]:0;
        })];
        for (const step of res.steps) {
          for (const [u,v] of step.pathNodes) { cap2[u][v]-=step.pathFlow; cap2[v][u]+=step.pathFlow; }
          edgeResiduals.push(g.edges.map(([ul,vl])=>{
            const ui=idxMap[ul],vi=idxMap[vl];
            return (ui!==undefined&&vi!==undefined)?cap2[ui][vi]:0;
          }));
        }
        setResult({ maxFlow:res.max_flow||res.maxFlow, steps:res.steps.map(s=>({...s,pathEdgeIndices:new Set(s.pathEdgeIndices)})), flow:res.flow, idxMap, initCap, edgeResiduals });
        setShowFlow(true);
      }
      toast_(`Graphe "${g.name}" chargé`);
    } catch(e) {
      toast_(e.message, "err");
    } finally {
      setApiLoading(false);
    }
  }

  // ── Sauvegarder le graphe en cours ──────────────────────────────────────
  async function saveGraph(name) {
    setShowSave(false);
    if (!apiOk) return toast_("Backend non disponible", "err");
    setApiLoading(true);
    try {
      const body = {
        name: name || graphName || "Sans titre",
        source_node: sourceNode, sink_node: sinkNode,
        nodes, edges, positions: nodePos,
      };
      const r = await fetch(`${API}/graphs`, { method:"POST", headers:{"Content-Type":"application/json"}, body:JSON.stringify(body) });
      const d = await r.json();
      if (!d.ok) throw new Error(d.error);
      setCurrentGraphId(d.data.id);
      setGraphName(name);
      toast_(`Graphe "${name}" sauvegardé`);
    } catch(e) {
      toast_(e.message, "err");
    } finally {
      setApiLoading(false);
    }
  }

  // ── Charger graphe par défaut depuis backend ──────────────────────────────
  async function loadDefault() {
    if (!apiOk) {
      setNodes([...DEFAULT_NODES]); setEdges(DEFAULT_EDGES.map(e=>[...e]));
      setSourceNode("α"); setSinkNode("ω"); setNodePos({...DEFAULT_POS});
      setResult(null); setCurrentStep(-1); setShowFlow(false);
      setCurrentGraphId(null);
      setSelectedNode(null);
      toast_("Données réinitialisées (hors ligne)");
      return;
    }
    setApiLoading(true);
    try {
      const r = await fetch(`${API}/default`, { method:"POST" });
      const d = await r.json();
      if (!d.ok) throw new Error(d.error);
      await loadGraph(d.data.id);
    } catch(e) {
      toast_(e.message,"err");
    } finally {
      setApiLoading(false);
    }
  }

  // ── Gestionnaire de clic sur nœud ──────────────────────────────────────
  const handleNodeClick = (node) => {
    if (selectedNode === node) {
      setSelectedNode(null);
    } else {
      setSelectedNode(node);
    }
  };

  // ── Nœuds ────────────────────────────────────────────────────────────────
  async function addNode() {
    const n = newNode.trim().toUpperCase();
    if (!n) return setErrors({node:"Nom requis"});
    if (nodes.includes(n)) return setErrors({node:`"${n}" existe déjà`});
    const updated = [...nodes, n];
    const idx = updated.length - 1;
    const cols = Math.ceil(Math.sqrt(updated.length));
    const p = { x:80+(idx%cols)*130, y:80+Math.floor(idx/cols)*120 };
    setNodes(updated);
    setNodePos(prev=>({...prev,[n]:p}));
    setNewNode(""); setErrors({}); setResult(null);

    if (apiOk && currentGraphId) {
      try {
        await fetch(`${API}/graphs/${currentGraphId}/nodes`, {
          method:"POST", headers:{"Content-Type":"application/json"},
          body: JSON.stringify({label:n, x:p.x, y:p.y})
        });
      } catch {}
    }
    toast_(`Noeud "${n}" ajouté`);
  }

  async function removeNode(n) {
    if (n===sourceNode||n===sinkNode) return toast_("Impossible : source ou puits","err");
    setNodes(nodes.filter(x=>x!==n));
    setEdges(edges.filter(([u,v])=>u!==n&&v!==n));
    setNodePos(p=>{ const q={...p}; delete q[n]; return q; });
    setResult(null);
    if (selectedNode === n) setSelectedNode(null);

    if (apiOk && currentGraphId) {
      try {
        await fetch(`${API}/graphs/${currentGraphId}/nodes/${encodeURIComponent(n)}`, { method:"DELETE" });
      } catch {}
    }
    toast_(`"${n}" supprimé`, "warn");
  }

  // ── Arcs ─────────────────────────────────────────────────────────────────
  async function addEdge() {
    const {from,to,cap} = newEdge;
    const errs = {};
    if (!from) errs.from="Requis";
    if (!to) errs.to="Requis";
    if (from&&to&&from===to) errs.to="Source ≠ Destination";
    const c = parseInt(cap);
    if (!cap||isNaN(c)||c<=0) errs.cap="Capacité > 0";
    if (Object.keys(errs).length) return setErrors(errs);
    if (edges.some(([u,v])=>u===from&&v===to)) return setErrors({from:"Arc déjà existant"});

    let dbId = null;
    if (apiOk && currentGraphId) {
      try {
        const r = await fetch(`${API}/graphs/${currentGraphId}/edges`, {
          method:"POST", headers:{"Content-Type":"application/json"},
          body: JSON.stringify({u:from, v:to, capacity:c})
        });
        const d = await r.json();
        if (d.ok) dbId = d.data.id;
      } catch {}
    }

    setEdges(prev=>[...prev,[from,to,c]]);
    setEdgeIds(prev=>[...prev,dbId]);
    setNewEdge({from:"",to:"",cap:""}); setErrors({}); setResult(null);
    toast_(`Arc ${from}→${to} (${c}) ajouté`);
  }

  async function removeEdge(i) {
    if (apiOk && currentGraphId && edgeIds[i]) {
      try {
        await fetch(`${API}/graphs/${currentGraphId}/edges/${edgeIds[i]}`, { method:"DELETE" });
      } catch {}
    }
    setEdges(edges.filter((_,j)=>j!==i));
    setEdgeIds(edgeIds.filter((_,j)=>j!==i));
    setResult(null);
    toast_("Arc supprimé","warn");
  }

  function startEdit(i) { setEditEdge(i); setEditCap(String(edges[i][2])); }

  async function saveEdit() {
    const c = parseInt(editCap);
    if (isNaN(c)||c<=0) return setErrors({editCap:"Capacité > 0"});

    if (apiOk && currentGraphId && edgeIds[editEdge]) {
      try {
        await fetch(`${API}/graphs/${currentGraphId}/edges/${edgeIds[editEdge]}`, {
          method:"PUT", headers:{"Content-Type":"application/json"},
          body: JSON.stringify({capacity:c})
        });
      } catch {}
    }
    setEdges(edges.map((e,i)=>i===editEdge?[e[0],e[1],c]:e));
    setEditEdge(null); setErrors({}); setResult(null);
    toast_("Capacité mise à jour");
  }

  // ── Calcul (backend prioritaire, fallback local) ──────────────────────────
  async function solve() {
    clearInterval(timerRef.current); setRunning(false);
    setSelectedNode(null);

    if (apiOk && currentGraphId) {
      setApiLoading(true);
      try {
        const r = await fetch(`${API}/graphs/${currentGraphId}/compute`, { method:"POST" });
        const d = await r.json();
        if (!d.ok) throw new Error(d.error);
        const data = d.data;
        const stepsFixed = data.steps.map(s=>({
          ...s,
          pathEdgeIndices: new Set(s.pathEdgeIndices),
        }));
        setResult({...data, steps:stepsFixed});
        setCurrentStep(-1); setShowFlow(true);
        toast_(`Flot maximal : ${data.maxFlow} (via serveur)`);
      } catch(e) {
        toast_(e.message,"err");
      } finally {
        setApiLoading(false);
      }
    } else {
      const r = edmondsKarpLocal(nodes, edges, sourceNode, sinkNode);
      if (!r) return toast_("Source ou puits invalide","err");
      setResult(r); setCurrentStep(-1); setShowFlow(true);
      toast_(`Flot maximal : ${r.maxFlow} (calcul local)`);
    }
  }

  function resetResult() {
    clearInterval(timerRef.current);
    setResult(null); setCurrentStep(-1); setRunning(false); setShowFlow(false);
    setSelectedNode(null);
  }

  function playAnim() {
    if (!result) return;
    setShowFlow(false); setCurrentStep(0); setRunning(true);
    setSelectedNode(null);
  }

  useEffect(() => {
    if (!running||!result) return;
    timerRef.current = setInterval(()=>{
      setCurrentStep(prev=>{
        if (prev>=result.steps.length-1) {
          clearInterval(timerRef.current); setRunning(false); setShowFlow(true); return prev;
        }
        return prev+1;
      });
    }, speed);
    return ()=>clearInterval(timerRef.current);
  }, [running, result, speed]);

  function flowAtStep(s) {
    if (!result||s<0) return null;
    const n=nodes.length, {idxMap}=result;
    const initCap=Array.from({length:n},()=>new Array(n).fill(0));
    for (const [u,v,c] of edges)
      if (idxMap[u]!==undefined&&idxMap[v]!==undefined)
        initCap[idxMap[u]][idxMap[v]]=c;
    const cap=initCap.map(r=>[...r]);
    for (let i=0;i<=s;i++)
      for (const [u,v] of result.steps[i].pathNodes) {
        cap[u][v]-=result.steps[i].pathFlow;
        cap[v][u]+=result.steps[i].pathFlow;
      }
    const f=Array.from({length:n},()=>new Array(n).fill(0));
    for (let u=0;u<n;u++)
      for (let v=0;v<n;v++)
        if (initCap[u][v]>0) f[u][v]=initCap[u][v]-cap[u][v];
    return f;
  }

  const displayFlow = running && currentStep >= 0 ? flowAtStep(currentStep) : (result ? result.flow : null);
  const highlightPath = running && currentStep >= 0 && result ? result.steps[currentStep].pathNodes : [];

  function newGraph() {
    clearInterval(timerRef.current);
    setNodes([]); setEdges([]); setEdgeIds([]);
    setSourceNode(""); setSinkNode("");
    setNodePos({}); setCurrentGraphId(null); setGraphName("");
    setResult(null); setCurrentStep(-1); setShowFlow(false);
    setSelectedNode(null);
  }

  return (
    <div className="min-h-screen p-4 md:p-6" style={{background:C.bg,color:C.text,fontFamily:"'Inter',sans-serif"}}>
      <div className="max-w-6xl mx-auto">

        {toast && (
          <div className="fixed top-5 right-5 z-50 px-5 py-3 rounded-2xl text-sm font-semibold shadow-2xl"
            style={{background:toast.type==="err"?"#fef2f2":toast.type==="warn"?"#fffbeb":C.accentDim,
              color:toast.type==="err"?C.red:toast.type==="warn"?C.orange:C.accent,
              border:`1px solid ${toast.type==="err"?C.red:toast.type==="warn"?C.orange:C.accent}`}}>
            {toast.type==="err"?"✗ ":toast.type==="warn"?"⚠ ":"✓ "}{toast.msg}
          </div>
        )}
        {showSave && <SaveModal onSave={saveGraph} onClose={()=>setShowSave(false)} />}

        {/* Header */}
        <div className="mb-4 flex flex-col md:flex-row items-center justify-between gap-3">
          <div className="text-center md:text-left">
            <span className="inline-block px-3 py-1 rounded-full text-xs font-bold mb-1"
              style={{background:C.accentDim,color:C.accent}}>Recherche Operationnelle</span>
            <h1 className="text-3xl md:text-4xl font-black tracking-tight">Flot Maximum</h1>
            <p className="text-sm mt-0.5" style={{color:C.muted}}>
               (Tableau) · {nodes.length} noeuds · {edges.length} arcs
              {graphName && <span style={{color:C.accent}}> · {graphName}</span>}
            </p>
          </div>
          <div className="flex flex-wrap items-center gap-2">
            <span className="text-xs px-3 py-1.5 rounded-full font-semibold"
              style={{background:apiOk?"#ccfbf1":"#fffbeb",color:apiOk?C.green:C.orange,border:`1px solid ${apiOk?C.green:C.orange}`}}>
              {apiOk?"● Backend connecté":"● Mode hors ligne"}
            </span>
            {apiOk && currentGraphId && (
              <Btn onClick={()=>setShowSave(true)} sm color={C.accentDim} textColor={C.accent}>Sauvegarder</Btn>
            )}
            {apiOk && !currentGraphId && (
              <Btn onClick={()=>setShowSave(true)} sm color={C.accentDim} textColor={C.accent}>Creer graphe</Btn>
            )}
          </div>
        </div>

        {/* Bannière FLOT COMPLET */}
        {flowComplete && (
          <div className="mb-5 p-4 rounded-2xl text-center border-2 animate-pulse"
            style={{background:"linear-gradient(135deg,#ccfbf1 0%,#99f6e4 100%)",borderColor:C.green}}>
            <div className="flex items-center justify-center gap-4">
              <div>
                <div className="text-2xl font-black" style={{color:C.green}}>Flot Max</div>
                <div className="text-sm" style={{color:C.muted}}>
                  Tout chemin de <strong style={{color:C.nodeSource}}>α</strong> à <strong style={{color:C.green}}>ω</strong> comporte au moins un arc saturé
                </div>
              </div>
            </div>
          </div>
        )}

        {/* Loader */}
        {apiLoading && (
          <div className="mb-3 px-4 py-2 rounded-xl text-sm text-center" style={{background:C.accentDim,color:C.accent}}>
            Chargement en cours…
          </div>
        )}

        {/* Tabs */}
        <div className="flex gap-2 flex-wrap mb-5 p-1 rounded-2xl" style={{background:C.panel}}>
          {[
            {k:"graph",    l:"Graphe & Resultats"},
            {k:"tableau",  l:"Tableau"},
            {k:"nodes",    l:"Noeuds"},
            {k:"edges",    l:"Arcs"},
            {k:"config",   l:"Config"},
            {k:"saved",    l:"Graphes"},
          ].map(t=><TabBtn key={t.k} label={t.l} active={tab===t.k} onClick={()=>setTab(t.k)} />)}
        </div>

        {/* ══ TAB GRAPHE ══════════════════════════════════════════════════════ */}
        {tab==="graph" && (
          <div>
            {/* Légende */}
            <div className="flex flex-wrap gap-4 justify-center mb-4 text-xs font-semibold">
              {[
                {col:C.nodeSource, label:`Source (${sourceNode}) / Puits (${sinkNode})`, circle:true},
                {col:C.arcFull, label:"Arc sature (ROUGE)"},
                {col:C.flowHighlight, label:"Arc flot partiel (VERT)"},
                {col:C.arcBlue, label:"Arc flot = 0 (BLEU)"},
                {col:C.arcPath, label:"Chemin augmentant (OR)"},
                {col:C.purple, label:"Élément sélectionné"},
              ].map(({col,label,circle})=>(
                <span key={label} className="flex items-center gap-1.5">
                  {circle
                    ? <span className="w-4 h-4 rounded-full border-2 inline-block" style={{background:col,borderColor:"#b45309"}} />
                    : <span className="inline-block" style={{width:24,height:3,background:col,borderRadius:2}} />}
                  {label}
                </span>
              ))}
              <span className="flex items-center gap-1.5" style={{color:C.muted}}>
                Format : <span style={{color:C.flowHighlight}}>cap(flot)</span>
              </span>
            </div>

            <div className="grid grid-cols-1 lg:grid-cols-3 gap-4">
              <div className="lg:col-span-2 rounded-2xl p-3 border" style={{borderColor:C.border,background:C.panel}}>
                <GraphSVG 
                  nodes={nodes} 
                  edges={edges} 
                  pos={nodePos}
                  flow={displayFlow} 
                  result={result} 
                  highlightPath={highlightPath}
                  sourceNode={sourceNode} 
                  sinkNode={sinkNode}
                  showFlow={showFlow||(running&&currentStep>=0)}
                  onNodeClick={handleNodeClick}
                  selectedNode={selectedNode}
                />
                <div className="text-xs text-center mt-2" style={{color:C.muted}}>
                  💡 Cliquez sur un <strong style={{color:C.purple}}>nœud</strong> pour voir tous les résultats détaillés
                </div>
              </div>
              <div className="lg:col-span-1">
                <NodeDetailsPanel 
                  node={selectedNode}
                  result={result}
                  nodes={nodes}
                  edges={edges}
                  sourceNode={sourceNode}
                  sinkNode={sinkNode}
                  onClose={() => setSelectedNode(null)}
                />
              </div>
            </div>

            <div className="flex flex-wrap gap-3 justify-center mt-4">
              <Btn onClick={solve} disabled={apiLoading}>Calculer Flot Max</Btn>
              {result && !running && (
                <Btn onClick={playAnim} color="#7c3aed" textColor="#fff">Animer BFS</Btn>
              )}
              {running && (
                <Btn onClick={()=>{clearInterval(timerRef.current);setRunning(false);setShowFlow(true);}} color={C.red} textColor="#fff">Pause</Btn>
              )}
              {result && !running && (
                <Btn onClick={()=>setShowFlow(s=>!s)} color={showFlow?"#e8f0fe":C.accentDim} textColor={showFlow?C.arcBlue:C.accent}>
                  {showFlow?"Masquer flots":"Afficher cap(flot)"}
                </Btn>
              )}
              {result && <Btn onClick={resetResult} color={C.border} textColor={C.text}>Effacer</Btn>}
              <label className="flex items-center gap-2 text-sm" style={{color:C.muted}}>
                Vitesse :
                <select value={speed} onChange={e=>setSpeed(+e.target.value)}
                  className="rounded-lg px-2 py-1.5 text-sm"
                  style={{background:C.panel2,border:`1px solid ${C.border}`,color:C.text}}>
                  <option value={1500}>Lente</option>
                  <option value={900}>Normale</option>
                  <option value={400}>Rapide</option>
                </select>
              </label>
            </div>

            {result && (
              <>
                <div className="rounded-2xl mt-5 p-5 flex flex-col md:flex-row items-center justify-between gap-4 border"
                  style={{background:"#ccfbf1",borderColor:C.green}}>
                  <div>
                    <div className="text-xs font-bold mb-1" style={{color:C.green}}>FLOT MAXIMAL</div>
                    <div className="text-6xl font-black leading-none" style={{color:C.green}}>{result.maxFlow}</div>
                    <div className="text-sm mt-1" style={{color:C.muted}}>milliers de m³/jour</div>
                  </div>
                  <div className="flex gap-6 text-center">
                    <div>
                      <div className="text-3xl font-black" style={{color:C.accent}}>{result.steps.length}</div>
                      <div className="text-xs" style={{color:C.muted}}>itérations </div>
                    </div>
                    <div>
                      <div className="text-3xl font-black" style={{color:C.purple}}>{nodes.length}</div>
                      <div className="text-xs" style={{color:C.muted}}>noeuds</div>
                    </div>
                    <div>
                      <div className="text-3xl font-black" style={{color:C.orange}}>{edges.length}</div>
                      <div className="text-xs" style={{color:C.muted}}>arcs</div>
                    </div>
                  </div>
                </div>

                <div className="rounded-2xl border overflow-hidden mt-5" style={{borderColor:C.border}}>
                  <div className="px-5 py-3 flex items-center gap-3" style={{background:C.panel,borderBottom:`1px solid ${C.border}`}}>
                    <span className="font-bold text-sm">Chemins augmentants (BFS)</span>
                    {currentStep>=0 && (
                      <span className="text-xs px-2 py-1 rounded-full" style={{background:C.accentDim,color:C.accent}}>
                        Étape {currentStep+1}/{result.steps.length}
                      </span>
                    )}
                    {selectedNode && (
                      <span className="text-xs px-2 py-1 rounded-full" style={{background:C.purple,color:"#fff"}}>
                        {selectedNode} sélectionné
                      </span>
                    )}
                  </div>
                  <div className="overflow-x-auto">
                    <table className="w-full text-sm">
                      <thead>
                        <tr style={{background:C.bg}}>
                          {["#","Chemin","Δ flot","Cumulé"].map(h=>(
                            <th key={h} className="px-4 py-2.5 text-left text-xs font-bold" style={{color:C.muted}}>{h}</th>
                          ))}
                        </tr>
                      </thead>
                      <tbody>
                        {result.steps.map((s,i)=>{
                          const active=i===currentStep,past=i<currentStep;
                          // Vérifier si le chemin passe par le nœud sélectionné
                          const passesThroughSelected = selectedNode && 
                            s.path.includes(selectedNode);
                          return (
                            <tr key={i} 
                              className={`cursor-pointer transition-all ${passesThroughSelected ? 'border-l-4 border-purple-500' : ''}`}
                              style={{
                                background: active ? "#dbeafe" : (passesThroughSelected ? "#f5f3ff" : (past ? "#ccfbf1" : "transparent")),
                                borderBottom: `1px solid ${C.border}`,
                              }}>
                              <td className="px-4 py-2.5 font-mono text-xs" style={{color:C.muted}}>{i+1}</td>
                              <td className="px-4 py-2.5 font-mono text-xs" style={{color:active?C.arcPath:C.text}}>
                                {sourceNode} → {s.path} → {sinkNode}
                                {passesThroughSelected && (
                                  <span className="ml-2 px-1.5 py-0.5 rounded text-xs" style={{background:C.purple,color:"#fff"}}>
                                    ✓ {selectedNode}
                                  </span>
                                )}
                              </td>
                              <td className="px-4 py-2.5 font-bold" style={{color:C.flowHighlight}}>+{s.pathFlow}</td>
                              <td className="px-4 py-2.5 font-bold" style={{color:past||active?C.green:C.muted}}>{s.totalFlow}</td>
                            </tr>
                          );
                        })}
                      </tbody>
                    </table>
                  </div>
                  {selectedNode && (
                    <div className="px-4 py-2 text-xs" style={{background:C.purple,color:"#fff"}}>
                      🟣 Les lignes violettes contiennent le nœud <strong>{selectedNode}</strong>
                    </div>
                  )}
                </div>
              </>
            )}

            {!result && (
              <div className="text-center py-14 rounded-2xl border mt-5" style={{borderColor:C.border,background:C.panel}}>
                <div className="text-5xl mb-3">🌊</div>
                <p className="font-semibold mb-1">{nodes.length} noeuds · {edges.length} arcs</p>
                <p className="text-sm" style={{color:C.muted}}>
                  Source : <strong style={{color:C.accent}}>{sourceNode||"—"}</strong> · Puits : <strong style={{color:C.green}}>{sinkNode||"—"}</strong>
                </p>
                <p className="text-xs mt-3" style={{color:C.muted}}>Cliquez sur <strong style={{color:C.accent}}>Calculer Flot Max</strong></p>
                <p className="text-xs mt-1" style={{color:C.muted}}>💡 Cliquez ensuite sur un <strong style={{color:C.purple}}>nœud</strong> pour voir les résultats détaillés</p>
              </div>
            )}
          </div>
        )}

        {/* ══ TAB TABLEAU BFS ════════════════════════════════════════════════ */}
        {tab==="tableau" && (
          <div>
            {!result && (
              <div className="text-center py-14 rounded-2xl border" style={{borderColor:C.border,background:C.panel}}>
                <div className="text-5xl mb-3">📋</div>
                <p className="font-semibold mb-1">Aucun résultat disponible</p>
                <p className="text-sm" style={{color:C.muted}}>
                  Allez dans <strong style={{color:C.accent}}>Graphe & Resultats</strong> et cliquez sur <strong style={{color:C.accent}}>Calculer Flot Max</strong>.
                </p>
              </div>
            )}
            {result && (
              <div>
                <div className="mb-4 p-4 rounded-2xl border" style={{background:C.panel,borderColor:C.border}}>
                  <h2 className="font-bold text-lg mb-1" style={{color:C.accent}}>Tableau des capacités résiduelles (Edmonds-Karp)</h2>
                  <p className="text-sm" style={{color:C.muted}}>
                    Chaque colonne = une itération BFS.
                    <span style={{color:"#fff",background:"#dc2626",padding:"0 4px",borderRadius:3,marginLeft:4}}>rouge</span> = goulot ·
                    <span style={{color:"#fff",background:"#2563eb",padding:"0 4px",borderRadius:3,marginLeft:4}}>bleue</span> = arc du chemin ·
                    <span style={{color:"#dc2626",fontWeight:"bold",marginLeft:4}}>S</span> = saturé
                  </p>
                </div>
                <BFSTableau result={result} edges={edges} nodes={nodes} sourceNode={sourceNode} sinkNode={sinkNode} />
              </div>
            )}
          </div>
        )}

        {/* ══ TAB NŒUDS ══════════════════════════════════════════════════════ */}
        {tab==="nodes" && (
          <div className="grid md:grid-cols-2 gap-6">
            <div className="rounded-2xl border p-5" style={{background:C.panel,borderColor:C.border}}>
              <h2 className="font-bold mb-4" style={{color:C.accent}}>Ajouter un noeud</h2>
              <div className="flex flex-col gap-3">
                <Field label="Nom du noeud (ex: X, N1)" error={errors.node}>
                  <Inp value={newNode} onChange={setNewNode} placeholder="Identifiant unique…" />
                </Field>
                <Btn onClick={addNode}>Ajouter</Btn>
              </div>
            </div>
            <div className="rounded-2xl border p-5" style={{background:C.panel,borderColor:C.border}}>
              <h2 className="font-bold mb-4">Noeuds <span className="text-xs font-normal ml-1" style={{color:C.muted}}>({nodes.length})</span></h2>
              <div className="flex flex-wrap gap-2">
                {nodes.map(n=>{
                  const isSrc=n===sourceNode,isSnk=n===sinkNode;
                  const isSelected = selectedNode === n;
                  return (
                    <div 
                      key={n} 
                      onClick={() => handleNodeClick(n)}
                      className={`flex items-center gap-1.5 px-3 py-1.5 rounded-xl text-sm font-bold cursor-pointer transition-all`}
                      style={{
                        background: isSelected ? C.accentDim : (isSrc||isSnk ? "#fffbeb" : C.panel2),
                        border: `1.5px solid ${isSelected ? C.purple : (isSrc||isSnk ? C.nodeSource : C.border)}`,
                        color: isSelected ? C.purple : (isSrc||isSnk ? C.nodeSource : C.text),
                        transform: isSelected ? 'scale(1.05)' : 'scale(1)',
                      }}>
                      {n}
                      {(isSrc||isSnk)
                        ? <span className="text-xs opacity-60">{isSrc?" (α)":" (ω)"}</span>
                        : <button onClick={(e)=>{e.stopPropagation();removeNode(n);}} className="ml-1 rounded-full w-4 h-4 text-xs" style={{color:C.red}}>✕</button>}
                    </div>
                  );
                })}
              </div>
            </div>
          </div>
        )}

        {/* ══ TAB ARCS ═══════════════════════════════════════════════════════ */}
        {tab==="edges" && (
          <div className="grid md:grid-cols-2 gap-6">
            <div className="rounded-2xl border p-5" style={{background:C.panel,borderColor:C.border}}>
              <h2 className="font-bold mb-4" style={{color:C.accent}}>Ajouter un arc</h2>
              <div className="flex flex-col gap-3">
                <Field label="Noeud source" error={errors.from}>
                  <Sel value={newEdge.from} onChange={v=>setNewEdge({...newEdge,from:v})} options={nodes} />
                </Field>
                <Field label="Noeud destination" error={errors.to}>
                  <Sel value={newEdge.to} onChange={v=>setNewEdge({...newEdge,to:v})} options={nodes} />
                </Field>
                <Field label="Capacité maximale" error={errors.cap}>
                  <Inp type="number" value={newEdge.cap} onChange={v=>setNewEdge({...newEdge,cap:v})} placeholder="ex: 15" />
                </Field>
                <Btn onClick={addEdge}>Ajouter l'arc</Btn>
              </div>
            </div>
            <div className="rounded-2xl border overflow-hidden" style={{background:C.panel,borderColor:C.border}}>
              <div className="px-5 py-3" style={{borderBottom:`1px solid ${C.border}`}}>
                <span className="font-bold text-sm">Arcs</span>
                <span className="ml-2 text-xs" style={{color:C.muted}}>({edges.length})</span>
              </div>
              <div className="overflow-y-auto" style={{maxHeight:400}}>
                <table className="w-full text-sm">
                  <thead>
                    <tr style={{background:C.bg}}>
                      {["De","Vers","Cap","Actions"].map(h=>(
                        <th key={h} className="px-3 py-2 text-left text-xs font-bold" style={{color:C.muted}}>{h}</th>
                      ))}
                    </tr>
                  </thead>
                  <tbody>
                    {edges.map(([u,v,c],i)=>(
                      <tr key={i} style={{borderBottom:`1px solid ${C.border}`}}>
                        <td className="px-3 py-2 font-mono font-bold" style={{color:C.arcRed}}>{u}</td>
                        <td className="px-3 py-2 font-mono font-bold" style={{color:C.arcBlue}}>{v}</td>
                        <td className="px-3 py-2">
                          {editEdge===i
                            ? <div className="flex gap-1 items-center">
                                <input type="number" value={editCap} onChange={e=>setEditCap(e.target.value)}
                                  className="rounded px-2 py-1 w-16 text-xs"
                                  style={{background:C.bg,border:`1px solid ${C.accent}`,color:C.text}} />
                                {errors.editCap && <span className="text-xs" style={{color:C.red}}>{errors.editCap}</span>}
                              </div>
                            : <span className="font-bold">{c}</span>}
                        </td>
                        <td className="px-3 py-2">
                          <div className="flex gap-1">
                            {editEdge===i
                              ? <>
                                  <Btn onClick={saveEdit} sm color={C.green} textColor="#fff">✓</Btn>
                                  <Btn onClick={()=>{setEditEdge(null);setErrors({});}} sm color={C.border} textColor={C.text}>✕</Btn>
                                </>
                              : <>
                                  <Btn onClick={()=>startEdit(i)} sm color={C.accentDim} textColor={C.accent}>✎</Btn>
                                  <Btn onClick={()=>removeEdge(i)} sm color="#fef2f2" textColor={C.red}>✕</Btn>
                                </>}
                          </div>
                        </td>
                      </tr>
                    ))}
                  </tbody>
                </table>
              </div>
            </div>
          </div>
        )}

        {/* ══ TAB CONFIG ═════════════════════════════════════════════════════ */}
        {tab==="config" && (
          <div className="grid md:grid-cols-2 gap-6">
            <ConfigForm nodes={nodes} sourceNode={sourceNode} sinkNode={sinkNode}
              onApply={(src,snk)=>{
                if (!src||!snk) return toast_("Sélectionner source et puits","err");
                if (src===snk) return toast_("Source ≠ Puits","err");
                setSourceNode(src); setSinkNode(snk); setResult(null);
                setSelectedNode(null);
                if (apiOk && currentGraphId) {
                  fetch(`${API}/graphs/${currentGraphId}`, {
                    method:"PUT", headers:{"Content-Type":"application/json"},
                    body:JSON.stringify({name:graphName,source_node:src,sink_node:snk})
                  }).catch(()=>{});
                }
                toast_(`Source: ${src} · Puits: ${snk}`);
              }} />
            <div className="rounded-2xl border p-5" style={{background:C.panel,borderColor:C.border}}>
              <h2 className="font-bold mb-4">Resume</h2>
              {[
                {l:"Noeuds",v:nodes.length,c:C.accent},
                {l:"Arcs",v:edges.length,c:C.purple},
                {l:"Source (α)",v:sourceNode||"—",c:C.nodeSource},
                {l:"Puits (ω)",v:sinkNode||"—",c:C.green},
                {l:"Graphe ID",v:currentGraphId||"(non sauvegarde)",c:C.orange},
                {l:"Cap. totale depuis source",v:edges.filter(([u])=>u===sourceNode).reduce((s,[,,c])=>s+c,0),c:C.text},
              ].map(({l,v,c})=>(
                <div key={l} className="flex justify-between items-center py-2.5" style={{borderBottom:`1px solid ${C.border}`}}>
                  <span className="text-sm" style={{color:C.muted}}>{l}</span>
                  <span className="font-bold text-sm" style={{color:c}}>{v}</span>
                </div>
              ))}
              <div className="mt-4 flex flex-col gap-2">
                <Btn onClick={loadDefault} color="#fffbeb" textColor={C.orange} disabled={apiLoading}>
                  Charger le graphe par defaut
                </Btn>
                <Btn onClick={newGraph} color={C.border} textColor={C.text}>
                  Nouveau graphe vide
                </Btn>
              </div>
            </div>
          </div>
        )}

        {/* ══ TAB GRAPHES SAUVEGARDÉS ════════════════════════════════════════ */}
        {tab==="saved" && (
          <div className="rounded-2xl border p-5" style={{background:C.panel,borderColor:C.border}}>
            <SavedGraphsPanel
              currentId={currentGraphId}
              onLoad={loadGraph}
              onDelete={()=>{}}
              onNew={newGraph}
              apiOk={apiOk}
            />
            {!apiOk && (
              <div className="mt-4 p-4 rounded-xl text-sm" style={{background:C.panel2,color:C.orange,border:`1px solid ${C.orange}`}}>
                Attention: Le backend n'est pas accessible. Lancez <code>node server.js</code> puis rechargez la page.
              </div>
            )}
          </div>
        )}

        
      </div>
    </div>
  );
}