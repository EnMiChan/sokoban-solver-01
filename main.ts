// Sokoban solver: one program answers 5 instances (i001..i005) in one run.
//
// Approach (original code, written for this bounty):
//   - Every level is a hallway with 1-4 independent rooms off it (3-4 boxes
//     each). A box pushed out of a room can never come back, so rooms are
//     solved one at a time and the push counts add up.
//   - Each room is solved by breadth-first search over PUSHES: the first
//     solved state a FIFO search meets is push-optimal. States are the boxes'
//     squares plus the player's reachable region (named by its lowest square).
//     Two prunings, neither of which removes a solvable state:
//       * dead squares: a box that can never be pushed onto any goal;
//       * frozen 2x2 blocks of walls/boxes with a box off its goal.
//   - Budgets are counts of work, never the wall clock: a fixed number of
//     states per room (with one larger retry), so two runs write the same
//     bytes. No randomness, no clock, no environment reads for decisions.
//   - Fallbacks, all deterministic: A* over pushes with an admissible
//     heuristic (sum of per-box push-distances to the nearest goal), then a
//     greedy best-first push search, then a whole-level search when a level
//     does not split into rooms. A fallback only runs when the optimal
//     search gives up, so it never costs optimality on levels the BFS solves.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

// Directions, fixed order everywhere: up, down, left, right.
const DX = [0, 0, -1, 1];
const DY = [-1, 1, 0, 0];
const STEP = ['u', 'd', 'l', 'r'];

// Work budgets (states / expansions), never the clock.
const ROOM_BFS_STATES = 250_000;
const ROOM_BFS_RETRY = 1_000_000;
const ASTAR_EXPANSIONS = 400_000;
const GREEDY_EXPANSIONS = 400_000;
const WHOLE_BFS_STATES = 150_000;

interface Level {
  w: number;
  h: number;
  wall: Uint8Array;
  goals: number[];
  boxes: number[];
  player: number;
}

interface Solution {
  pushes: number;
  moves: string;
}

/** A level in XSB text (# wall, space floor, . goal, $ box, * box on a goal, @ player, + player on a goal). */
function parseLevel(text: string): Level {
  const rows = text.split('\n').filter((r) => r.length > 0);
  const h = rows.length;
  const w = Math.max(...rows.map((r) => r.length));
  const wall = new Uint8Array(w * h).fill(1);
  const goals: number[] = [];
  const boxes: number[] = [];
  let player = -1;
  rows.forEach((row, y) => {
    for (let x = 0; x < row.length; x++) {
      const ch = row[x];
      const i = y * w + x;
      if (ch === '#') continue;
      wall[i] = 0;
      if (ch === '.' || ch === '*' || ch === '+') goals.push(i);
      if (ch === '$' || ch === '*') boxes.push(i);
      if (ch === '@' || ch === '+') player = i;
    }
  });
  // The outer frame is wall whatever it shows: nothing leaves the board.
  for (let y = 0; y < h; y++) {
    for (let x = 0; x < w; x++) {
      if (x === 0 || y === 0 || x === w - 1 || y === h - 1) wall[y * w + x] = 1;
    }
  }
  boxes.sort((a, b) => a - b);
  goals.sort((a, b) => a - b);
  return { w, h, wall, goals, boxes, player };
}

/** The squares from which a box can be pushed onto some goal (pulled back from the goals over open floor). */
function liveSquares(w: number, wall: Uint8Array, goals: number[]): Uint8Array {
  const live = new Uint8Array(wall.length);
  const queue = [...goals];
  for (const g of goals) live[g] = 1;
  for (let qi = 0; qi < queue.length; qi++) {
    const x = queue[qi]!;
    for (let k = 0; k < 4; k++) {
      const d = DY[k]! * w + DX[k]!;
      const y = x - d; // a box here pushed along d lands on x; the player stands at y - d
      if (y < 0 || y >= wall.length) continue;
      if (!wall[y] && !wall[y - d] && !live[y]) {
        live[y] = 1;
        queue.push(y);
      }
    }
  }
  return live;
}

/** Push-distance from every square to its nearest goal, over the box-push graph (other boxes ignored). */
function pushDistances(w: number, wall: Uint8Array, goals: number[]): Int32Array {
  const dist = new Int32Array(wall.length).fill(-1);
  const queue = [...goals];
  for (const g of goals) dist[g] = 0;
  for (let qi = 0; qi < queue.length; qi++) {
    const x = queue[qi]!;
    for (let k = 0; k < 4; k++) {
      const d = DY[k]! * w + DX[k]!;
      const y = x - d; // a box at y pushed along d lands on x
      if (y < 0 || y >= wall.length) continue;
      if (!wall[y] && !wall[y - d] && dist[y] < 0) {
        dist[y] = dist[x]! + 1;
        queue.push(y);
      }
    }
  }
  return dist;
}

/** Whether the box just pushed to `t` sits in a frozen 2x2 block of walls and boxes with a box off its goal. */
function frozenBlock(w: number, wall: Uint8Array, occupied: Uint8Array, goal: Uint8Array, t: number): boolean {
  for (const a of [t, t - 1, t - w, t - w - 1]) {
    const b = a + 1;
    const c = a + w;
    const d = c + 1;
    if (a < 0 || d >= wall.length) continue;
    if (!(wall[a] || occupied[a]) || !(wall[b] || occupied[b]) || !(wall[c] || occupied[c]) || !(wall[d] || occupied[d])) continue;
    if ((occupied[a] && !goal[a]) || (occupied[b] && !goal[b]) || (occupied[c] && !goal[c]) || (occupied[d] && !goal[d])) return true;
  }
  return false;
}

/** The shortest walk from `from` to `to` around walls and boxes, in lower LURD letters (first direction first on ties). */
function walkTo(w: number, wall: Uint8Array, boxes: number[], from: number, to: number): string {
  if (from === to) return '';
  const occupied = new Uint8Array(wall.length);
  for (const b of boxes) occupied[b] = 1;
  const prev = new Int32Array(wall.length).fill(-1);
  const how = new Uint8Array(wall.length);
  const queue = [from];
  prev[from] = from;
  for (let qi = 0; qi < queue.length; qi++) {
    const p = queue[qi]!;
    if (p === to) break;
    for (let k = 0; k < 4; k++) {
      const q = p + DY[k]! * w + DX[k]!;
      if (wall[q] || occupied[q] || prev[q] !== -1) continue;
      prev[q] = p;
      how[q] = k;
      queue.push(q);
    }
  }
  if (prev[to] === -1) throw new Error('walkTo: the push square is out of reach');
  let s = '';
  for (let p = to; p !== from; p = prev[p]!) s = STEP[how[p]!] + s;
  return s;
}

/** The square the player stands on after `moves` (LURD, case aside) from `from` on a board `w` wide. */
function endOf(w: number, from: number, moves: string): number {
  let p = from;
  for (const ch of moves.toLowerCase()) p += ch === 'u' ? -w : ch === 'd' ? w : ch === 'l' ? -1 : 1;
  return p;
}

// Pack up to 4 sorted box squares (< 256 each) into one number; pad with 0xff.
function packBoxes(boxes: number[]): number {
  let p = 0xff;
  for (let i = boxes.length - 1; i >= 0; i--) p = p * 256 + boxes[i]!;
  return p;
}

function unpackBoxes(packed: number, n: number, out: number[]): void {
  for (let i = 0; i < n; i++) {
    out[i] = packed % 256;
    packed = Math.floor(packed / 256);
  }
}

/**
 * Push-optimal solution of `level` (at most `maxStates` states), by breadth-first search over pushes.
 * {pushes, moves} (moves in LURD: a lower letter a step, an upper one a push), or null when the search gives up.
 */
function solvePushBFS(lv: Level, maxStates: number): Solution | null {
  const { w, wall, goals } = lv;
  const size = wall.length;
  const n = lv.boxes.length;
  const goal = new Uint8Array(size);
  for (const g of goals) goal[g] = 1;
  const live = liveSquares(w, wall, goals);
  if (lv.boxes.some((b) => !live[b])) return null;
  const solved = (boxes: number[]): boolean => boxes.every((b) => goal[b]);
  if (solved(lv.boxes)) return { pushes: 0, moves: '' };

  const occupied = new Uint8Array(size);
  const seen = new Int32Array(size);
  const seenR = new Int32Array(size);
  const stack = new Int32Array(size);
  let stamp = 0;
  let stampR = 0;
  // Lowest square of the region reachable from `from` with `occupied` in the way.
  const regionLow = (from: number): number => {
    const s = ++stampR;
    let low = from;
    let top = 0;
    stack[top++] = from;
    seenR[from] = s;
    while (top > 0) {
      const p = stack[--top]!;
      if (p < low) low = p;
      const q0 = p - w;
      const q1 = p + w;
      const q2 = p - 1;
      const q3 = p + 1;
      if (!wall[q0] && !occupied[q0] && seenR[q0] !== s) { seenR[q0] = s; stack[top++] = q0; }
      if (!wall[q1] && !occupied[q1] && seenR[q1] !== s) { seenR[q1] = s; stack[top++] = q1; }
      if (!wall[q2] && !occupied[q2] && seenR[q2] !== s) { seenR[q2] = s; stack[top++] = q2; }
      if (!wall[q3] && !occupied[q3] && seenR[q3] !== s) { seenR[q3] = s; stack[top++] = q3; }
    }
    return low;
  };

  // The states in the order found: packed boxes, the player's square, parent, and the push that made them.
  const sBoxes: number[] = [packBoxes(lv.boxes)];
  const sPlayer: number[] = [lv.player];
  const sParent: number[] = [-1];
  const sPushFrom: number[] = [-1];
  const sPushDir: number[] = [-1];
  const index = new Map<number, number>();
  for (const b of lv.boxes) occupied[b] = 1;
  index.set(packBoxes(lv.boxes) * 256 + regionLow(lv.player), 0);
  for (const b of lv.boxes) occupied[b] = 0;

  const cur = new Array<number>(n);
  let found = -1;
  for (let head = 0; found < 0 && head < sBoxes.length; head++) {
    unpackBoxes(sBoxes[head]!, n, cur);
    for (const b of cur) occupied[b] = 1;
    const here = ++stamp;
    // Mark this state's region with `here` (same flood fill as regionLow, but keeping the stamp).
    {
      let top = 0;
      stack[top++] = sPlayer[head]!;
      seen[sPlayer[head]!] = here;
      while (top > 0) {
        const p = stack[--top]!;
        const q0 = p - w;
        const q1 = p + w;
        const q2 = p - 1;
        const q3 = p + 1;
        if (!wall[q0] && !occupied[q0] && seen[q0] !== here) { seen[q0] = here; stack[top++] = q0; }
        if (!wall[q1] && !occupied[q1] && seen[q1] !== here) { seen[q1] = here; stack[top++] = q1; }
        if (!wall[q2] && !occupied[q2] && seen[q2] !== here) { seen[q2] = here; stack[top++] = q2; }
        if (!wall[q3] && !occupied[q3] && seen[q3] !== here) { seen[q3] = here; stack[top++] = q3; }
      }
    }
    for (let bi = 0; bi < n && found < 0; bi++) {
      const b = cur[bi]!;
      for (let k = 0; k < 4; k++) {
        const d = DY[k]! * w + DX[k]!;
        const t = b + d;
        if (seen[b - d] !== here || wall[t] || occupied[t] || !live[t]) continue;
        occupied[b] = 0;
        occupied[t] = 1;
        const frozen = frozenBlock(w, wall, occupied, goal, t);
        let key = -1;
        let next = -1;
        if (!frozen) {
          const nb = cur.slice();
          nb[bi] = t;
          nb.sort((x, y) => x - y);
          next = packBoxes(nb);
          key = next * 256 + regionLow(b);
        }
        occupied[t] = 0;
        occupied[b] = 1;
        if (frozen || index.has(key)) continue;
        if (sBoxes.length >= maxStates) {
          for (const x of cur) occupied[x] = 0;
          return null;
        }
        index.set(key, sBoxes.length);
        sBoxes.push(next);
        sPlayer.push(b);
        sParent.push(head);
        sPushFrom.push(b);
        sPushDir.push(k);
        if (solved(cur.map((x, i) => (i === bi ? t : x)))) {
          found = sBoxes.length - 1;
          break;
        }
      }
    }
    for (const x of cur) occupied[x] = 0;
  }
  if (found < 0) return null;
  return { pushes: pathLength(sParent, found), moves: reconstruct(w, wall, lv, sParent, sPushFrom, sPushDir, found) };
}

function pathLength(parent: number[], s: number): number {
  let n = 0;
  for (let t = s; t > 0; t = parent[t]!) n++;
  return n;
}

/** The moves of a found state: walk to each push's square, then push. */
function reconstruct(w: number, wall: Uint8Array, lv: Level, parent: number[], pushFrom: number[], pushDir: number[], found: number): string {
  const path: number[] = [];
  for (let s = found; s > 0; s = parent[s]!) path.push(s);
  path.reverse();
  let moves = '';
  let player = lv.player;
  let boxes = lv.boxes.slice();
  for (const s of path) {
    const from = pushFrom[s]!;
    const k = pushDir[s]!;
    const d = DY[k]! * w + DX[k]!;
    moves += walkTo(w, wall, boxes, player, from - d);
    moves += STEP[k]!.toUpperCase();
    player = from;
    boxes[boxes.indexOf(from)] = from + d;
    boxes.sort((a, b) => a - b);
  }
  return moves;
}

/**
 * A* over pushes with the admissible heuristic "sum of per-box push-distances to the nearest goal"
 * (one push moves one box one edge, so it lowers the sum by at most 1). Optimal when it finishes
 * within `maxExpansions` expansions: a solved state is answered when it is popped, never when it is
 * made. Deterministic: ties go by (f, h, order).
 */
function solvePushAStar(lv: Level, maxExpansions: number): Solution | null {
  const { w, wall, goals } = lv;
  const size = wall.length;
  const n = lv.boxes.length;
  const goal = new Uint8Array(size);
  for (const g of goals) goal[g] = 1;
  const live = liveSquares(w, wall, goals);
  const dist = pushDistances(w, wall, goals);
  if (lv.boxes.some((b) => !live[b] || dist[b]! < 0)) return null;
  const solved = (boxes: number[]): boolean => boxes.every((b) => goal[b]);
  if (solved(lv.boxes)) return { pushes: 0, moves: '' };
  const hOf = (boxes: number[]): number => {
    let h = 0;
    for (const b of boxes) h += dist[b]!;
    return h;
  };

  const occupied = new Uint8Array(size);
  const seen = new Int32Array(size);
  const seenR = new Int32Array(size);
  const stack = new Int32Array(size);
  let stamp = 0;
  let stampR = 0;
  // Lowest square of the region reachable from `from` with `occupied` in the way.
  const regionLow = (from: number): number => {
    const s = ++stampR;
    let low = from;
    let top = 0;
    stack[top++] = from;
    seenR[from] = s;
    while (top > 0) {
      const p = stack[--top]!;
      if (p < low) low = p;
      const q0 = p - w;
      const q1 = p + w;
      const q2 = p - 1;
      const q3 = p + 1;
      if (!wall[q0] && !occupied[q0] && seenR[q0] !== s) { seenR[q0] = s; stack[top++] = q0; }
      if (!wall[q1] && !occupied[q1] && seenR[q1] !== s) { seenR[q1] = s; stack[top++] = q1; }
      if (!wall[q2] && !occupied[q2] && seenR[q2] !== s) { seenR[q2] = s; stack[top++] = q2; }
      if (!wall[q3] && !occupied[q3] && seenR[q3] !== s) { seenR[q3] = s; stack[top++] = q3; }
    }
    return low;
  };

  const sBoxes: number[] = [packBoxes(lv.boxes)];
  const sPlayer: number[] = [lv.player];
  const sParent: number[] = [-1];
  const sPushFrom: number[] = [-1];
  const sPushDir: number[] = [-1];
  const sG: number[] = [0];
  const sKey: number[] = [];
  const best = new Map<number, number>();
  for (const b of lv.boxes) occupied[b] = 1;
  const startKey = packBoxes(lv.boxes) * 256 + regionLow(lv.player);
  sKey.push(startKey);
  best.set(startKey, 0);
  for (const b of lv.boxes) occupied[b] = 0;

  // Heap of [f, h, order, state], smallest first.
  const heap: number[][] = [];
  const less = (a: number[], b: number[]): boolean =>
    a[0]! < b[0]! || (a[0]! === b[0]! && (a[1]! < b[1]! || (a[1]! === b[1]! && a[2]! < b[2]!)));
  const heapPush = (e: number[]): void => {
    let i = heap.length;
    heap.push(e);
    while (i > 0) {
      const p = (i - 1) >> 1;
      if (!less(heap[i]!, heap[p]!)) break;
      [heap[i], heap[p]] = [heap[p]!, heap[i]!];
      i = p;
    }
  };
  const heapPop = (): number[] => {
    const top = heap[0]!;
    const last = heap.pop()!;
    if (heap.length > 0) {
      heap[0] = last;
      for (let i = 0; ; ) {
        let c = 2 * i + 1;
        if (c >= heap.length) break;
        if (c + 1 < heap.length && less(heap[c + 1]!, heap[c]!)) c++;
        if (!less(heap[c]!, heap[i]!)) break;
        [heap[i], heap[c]] = [heap[c]!, heap[i]!];
        i = c;
      }
    }
    return top;
  };

  const h0 = hOf(lv.boxes);
  heapPush([h0, h0, 0, 0]);
  let order = 1;
  let expanded = 0;
  const cur = new Array<number>(n);
  while (heap.length > 0 && expanded < maxExpansions) {
    const [, , , s] = heapPop()!;
    if (best.get(sKey[s]!) !== s) continue; // stale: a better path to this state was found
    unpackBoxes(sBoxes[s]!, n, cur);
    if (solved(cur)) return { pushes: sG[s]!, moves: reconstruct(w, wall, lv, sParent, sPushFrom, sPushDir, s) };
    for (const b of cur) occupied[b] = 1;
    const here = ++stamp;
    {
      let top = 0;
      stack[top++] = sPlayer[s]!;
      seen[sPlayer[s]!] = here;
      while (top > 0) {
        const p = stack[--top]!;
        const q0 = p - w;
        const q1 = p + w;
        const q2 = p - 1;
        const q3 = p + 1;
        if (!wall[q0] && !occupied[q0] && seen[q0] !== here) { seen[q0] = here; stack[top++] = q0; }
        if (!wall[q1] && !occupied[q1] && seen[q1] !== here) { seen[q1] = here; stack[top++] = q1; }
        if (!wall[q2] && !occupied[q2] && seen[q2] !== here) { seen[q2] = here; stack[top++] = q2; }
        if (!wall[q3] && !occupied[q3] && seen[q3] !== here) { seen[q3] = here; stack[top++] = q3; }
      }
    }
    expanded++;
    for (let bi = 0; bi < n; bi++) {
      const b = cur[bi]!;
      for (let k = 0; k < 4; k++) {
        const d = DY[k]! * w + DX[k]!;
        const t = b + d;
        if (seen[b - d] !== here || wall[t] || occupied[t] || !live[t]) continue;
        occupied[b] = 0;
        occupied[t] = 1;
        const frozen = frozenBlock(w, wall, occupied, goal, t);
        let key = -1;
        let next = -1;
        let nh = 0;
        if (!frozen) {
          const nb = cur.slice();
          nb[bi] = t;
          nb.sort((x, y) => x - y);
          next = packBoxes(nb);
          nh = hOf(nb);
          key = next * 256 + regionLow(b);
        }
        occupied[t] = 0;
        occupied[b] = 1;
        if (frozen) continue;
        const g = sG[s]! + 1;
        const prev = best.get(key);
        if (prev !== undefined && sG[prev]! <= g) continue;
        const idx = sBoxes.length;
        sBoxes.push(next);
        sPlayer.push(b);
        sParent.push(s);
        sPushFrom.push(b);
        sPushDir.push(k);
        sG.push(g);
        sKey.push(key);
        best.set(key, idx);
        heapPush([g + nh, nh, order++, idx]);
      }
    }
    for (const x of cur) occupied[x] = 0;
  }
  return null;
}

/**
 * Greedy best-first push search (f = h only): not optimal, but finds a solution where the optimal
 * searches give up. Same pruning, same determinism.
 */
function solveGreedy(lv: Level, maxExpansions: number): Solution | null {
  const { w, wall, goals } = lv;
  const size = wall.length;
  const n = lv.boxes.length;
  const goal = new Uint8Array(size);
  for (const g of goals) goal[g] = 1;
  const live = liveSquares(w, wall, goals);
  const dist = pushDistances(w, wall, goals);
  if (lv.boxes.some((b) => !live[b] || dist[b]! < 0)) return null;
  const solved = (boxes: number[]): boolean => boxes.every((b) => goal[b]);
  if (solved(lv.boxes)) return { pushes: 0, moves: '' };
  const hOf = (boxes: number[]): number => {
    let h = 0;
    for (const b of boxes) h += dist[b]!;
    return h;
  };
  const occupied = new Uint8Array(size);
  const seen = new Int32Array(size);
  const seenR = new Int32Array(size);
  const stack = new Int32Array(size);
  let stamp = 0;
  let stampR = 0;
  const regionLow = (from: number): number => {
    const s = ++stampR;
    let low = from;
    let top = 0;
    stack[top++] = from;
    seenR[from] = s;
    while (top > 0) {
      const p = stack[--top]!;
      if (p < low) low = p;
      const q0 = p - w;
      const q1 = p + w;
      const q2 = p - 1;
      const q3 = p + 1;
      if (!wall[q0] && !occupied[q0] && seenR[q0] !== s) { seenR[q0] = s; stack[top++] = q0; }
      if (!wall[q1] && !occupied[q1] && seenR[q1] !== s) { seenR[q1] = s; stack[top++] = q1; }
      if (!wall[q2] && !occupied[q2] && seenR[q2] !== s) { seenR[q2] = s; stack[top++] = q2; }
      if (!wall[q3] && !occupied[q3] && seenR[q3] !== s) { seenR[q3] = s; stack[top++] = q3; }
    }
    return low;
  };
  const sBoxes: number[] = [packBoxes(lv.boxes)];
  const sPlayer: number[] = [lv.player];
  const sParent: number[] = [-1];
  const sPushFrom: number[] = [-1];
  const sPushDir: number[] = [-1];
  const sG: number[] = [0];
  const sKey: number[] = [];
  const best = new Map<number, number>();
  for (const b of lv.boxes) occupied[b] = 1;
  const startKey = packBoxes(lv.boxes) * 256 + regionLow(lv.player);
  sKey.push(startKey);
  best.set(startKey, 0);
  for (const b of lv.boxes) occupied[b] = 0;
  const heap: number[][] = [];
  const less = (a: number[], b: number[]): boolean =>
    a[0]! < b[0]! || (a[0]! === b[0]! && (a[1]! < b[1]! || (a[1]! === b[1]! && a[2]! < b[2]!)));
  const heapPush = (e: number[]): void => {
    let i = heap.length;
    heap.push(e);
    while (i > 0) {
      const p = (i - 1) >> 1;
      if (!less(heap[i]!, heap[p]!)) break;
      [heap[i], heap[p]] = [heap[p]!, heap[i]!];
      i = p;
    }
  };
  const heapPop = (): number[] => {
    const top = heap[0]!;
    const last = heap.pop()!;
    if (heap.length > 0) {
      heap[0] = last;
      for (let i = 0; ; ) {
        let c = 2 * i + 1;
        if (c >= heap.length) break;
        if (c + 1 < heap.length && less(heap[c + 1]!, heap[c]!)) c++;
        if (!less(heap[c]!, heap[i]!)) break;
        [heap[i], heap[c]] = [heap[c]!, heap[i]!];
        i = c;
      }
    }
    return top;
  };
  heapPush([hOf(lv.boxes), 0, 0, 0]);
  let order = 1;
  let expanded = 0;
  const cur = new Array<number>(n);
  while (heap.length > 0 && expanded < maxExpansions) {
    const [, , , s] = heapPop()!;
    if (best.get(sKey[s]!) !== s) continue; // stale: a better path to this state was found
    unpackBoxes(sBoxes[s]!, n, cur);
    for (const b of cur) occupied[b] = 1;
    const here = ++stamp;
    {
      let top = 0;
      stack[top++] = sPlayer[s]!;
      seen[sPlayer[s]!] = here;
      while (top > 0) {
        const p = stack[--top]!;
        const q0 = p - w;
        const q1 = p + w;
        const q2 = p - 1;
        const q3 = p + 1;
        if (!wall[q0] && !occupied[q0] && seen[q0] !== here) { seen[q0] = here; stack[top++] = q0; }
        if (!wall[q1] && !occupied[q1] && seen[q1] !== here) { seen[q1] = here; stack[top++] = q1; }
        if (!wall[q2] && !occupied[q2] && seen[q2] !== here) { seen[q2] = here; stack[top++] = q2; }
        if (!wall[q3] && !occupied[q3] && seen[q3] !== here) { seen[q3] = here; stack[top++] = q3; }
      }
    }
    expanded++;
    for (let bi = 0; bi < n; bi++) {
      const b = cur[bi]!;
      for (let k = 0; k < 4; k++) {
        const d = DY[k]! * w + DX[k]!;
        const t = b + d;
        if (seen[b - d] !== here || wall[t] || occupied[t] || !live[t]) continue;
        occupied[b] = 0;
        occupied[t] = 1;
        const frozen = frozenBlock(w, wall, occupied, goal, t);
        let key = -1;
        let next = -1;
        let nh = 0;
        if (!frozen) {
          const nb = cur.slice();
          nb[bi] = t;
          nb.sort((x, y) => x - y);
          next = packBoxes(nb);
          nh = hOf(nb);
          key = next * 256 + regionLow(b);
        }
        occupied[t] = 0;
        occupied[b] = 1;
        if (frozen) continue;
        const g = sG[s]! + 1;
        const prev = best.get(key);
        if (prev !== undefined && sG[prev]! <= g) continue;
        const idx = sBoxes.length;
        sBoxes.push(next);
        sPlayer.push(b);
        sParent.push(s);
        sPushFrom.push(b);
        sPushDir.push(k);
        sG.push(g);
        sKey.push(key);
        best.set(key, idx);
        if (solved(cur.map((x, i) => (i === bi ? t : x)))) {
          for (const x of cur) occupied[x] = 0;
          return { pushes: g, moves: reconstruct(w, wall, lv, sParent, sPushFrom, sPushDir, idx) };
        }
        heapPush([nh, g, order++, idx]);
      }
    }
    for (const x of cur) occupied[x] = 0;
  }
  return null;
}

/**
 * The level's rooms: cut the dead squares of the player's row (the hallway: a box there reaches no goal)
 * out of the floor; each part left that holds a box is a room. Null when some part holds more or fewer
 * boxes than goals, or a box starts in the hallway.
 */
function roomsOf(lv: Level): { boxes: number[]; goals: number[] }[] | null {
  const { w, wall, goals, boxes, player } = lv;
  const live = liveSquares(w, wall, goals);
  const row = Math.floor(player / w);
  const cut = new Uint8Array(wall.length);
  for (let x = 0; x < w; x++) {
    const i = row * w + x;
    if (!wall[i] && !live[i]) cut[i] = 1;
  }
  if (boxes.some((b) => cut[b])) return null;
  const part = new Int32Array(wall.length).fill(-1);
  const rooms: { boxes: number[]; goals: number[] }[] = [];
  for (let s = 0; s < wall.length; s++) {
    if (wall[s] || cut[s] || part[s] >= 0) continue;
    const squares = [s];
    part[s] = rooms.length;
    for (let i = 0; i < squares.length; i++) {
      const p = squares[i]!;
      for (let k = 0; k < 4; k++) {
        const q = p + DY[k]! * w + DX[k]!;
        if (!wall[q] && !cut[q] && part[q] < 0) {
          part[q] = rooms.length;
          squares.push(q);
        }
      }
    }
    rooms.push({ boxes: [], goals: [] });
  }
  for (const b of boxes) {
    if (part[b] < 0) return null;
    rooms[part[b]!]!.boxes.push(b);
  }
  for (const g of goals) {
    if (part[g] < 0) return null;
    rooms[part[g]!]!.goals.push(g);
  }
  if (rooms.some((r) => r.boxes.length !== r.goals.length)) return null;
  return rooms.filter((r) => r.boxes.length > 0);
}

/** One room's solution: optimal BFS first, larger retry, then A*, then greedy. */
function solveRoom(lv: Level): Solution | null {
  return (
    solvePushBFS(lv, ROOM_BFS_STATES) ??
    solvePushBFS(lv, ROOM_BFS_RETRY) ??
    solvePushAStar(lv, ASTAR_EXPANSIONS) ??
    solveGreedy(lv, GREEDY_EXPANSIONS)
  );
}

/** The level solved room by room: each room's solution in turn, the other rooms' boxes standing as walls. */
function solveByRooms(lv: Level): Solution | null {
  const rooms = roomsOf(lv);
  if (rooms === null) return null;
  let player = lv.player;
  let pushes = 0;
  let moves = '';
  const done = new Set<number>();
  for (let r = 0; r < rooms.length; r++) {
    const wall = lv.wall.slice();
    for (let o = 0; o < rooms.length; o++) {
      if (o === r) continue;
      const src = done.has(o) ? rooms[o]!.goals : rooms[o]!.boxes;
      for (const b of src) wall[b] = 1;
    }
    const sub: Level = {
      w: lv.w,
      h: lv.h,
      wall,
      goals: rooms[r]!.goals.slice().sort((a, b) => a - b),
      boxes: rooms[r]!.boxes.slice().sort((a, b) => a - b),
      player,
    };
    const sol = solveRoom(sub);
    if (sol === null) return null;
    pushes += sol.pushes;
    moves += sol.moves;
    player = endOf(lv.w, player, sol.moves);
    done.add(r);
  }
  return { pushes, moves };
}

/**
 * Whole-level fallback for a level that does not split into rooms: greedy best-first push search
 * with string keys (more than 4 boxes break the packed key). Same pruning, same determinism.
 */
function solveWhole(lv: Level): Solution | null {
  const { w, wall, goals } = lv;
  const size = wall.length;
  const goal = new Uint8Array(size);
  for (const g of goals) goal[g] = 1;
  const live = liveSquares(w, wall, goals);
  const dist = pushDistances(w, wall, goals);
  if (lv.boxes.some((b) => !live[b] || dist[b]! < 0)) return null;
  const solved = (boxes: number[]): boolean => boxes.every((b) => goal[b]);
  if (solved(lv.boxes)) return { pushes: 0, moves: '' };
  const hOf = (boxes: number[]): number => {
    let h = 0;
    for (const b of boxes) h += dist[b]!;
    return h;
  };

  const occupied = new Uint8Array(size);
  const seen = new Int32Array(size);
  const seenR = new Int32Array(size);
  const stack = new Int32Array(size);
  let stamp = 0;
  let stampR = 0;
  const regionLow = (from: number): number => {
    const s = ++stampR;
    let low = from;
    let top = 0;
    stack[top++] = from;
    seenR[from] = s;
    while (top > 0) {
      const p = stack[--top]!;
      if (p < low) low = p;
      const q0 = p - w;
      const q1 = p + w;
      const q2 = p - 1;
      const q3 = p + 1;
      if (!wall[q0] && !occupied[q0] && seenR[q0] !== s) { seenR[q0] = s; stack[top++] = q0; }
      if (!wall[q1] && !occupied[q1] && seenR[q1] !== s) { seenR[q1] = s; stack[top++] = q1; }
      if (!wall[q2] && !occupied[q2] && seenR[q2] !== s) { seenR[q2] = s; stack[top++] = q2; }
      if (!wall[q3] && !occupied[q3] && seenR[q3] !== s) { seenR[q3] = s; stack[top++] = q3; }
    }
    return low;
  };
  const keyOf = (boxes: number[], low: number): string => boxes.join(',') + '|' + low;

  const sBoxes: number[][] = [lv.boxes.slice()];
  const sPlayer: number[] = [lv.player];
  const sParent: number[] = [-1];
  const sPushFrom: number[] = [-1];
  const sPushDir: number[] = [-1];
  const sG: number[] = [0];
  const sKey: string[] = [];
  const best = new Map<string, number>();
  for (const b of lv.boxes) occupied[b] = 1;
  const startKey = keyOf(lv.boxes, regionLow(lv.player));
  sKey.push(startKey);
  best.set(startKey, 0);
  for (const b of lv.boxes) occupied[b] = 0;

  // Heap of [h, g, order, state], smallest first.
  const heap: number[][] = [];
  const less = (a: number[], b: number[]): boolean =>
    a[0]! < b[0]! || (a[0]! === b[0]! && (a[1]! < b[1]! || (a[1]! === b[1]! && a[2]! < b[2]!)));
  const heapPush = (e: number[]): void => {
    let i = heap.length;
    heap.push(e);
    while (i > 0) {
      const p = (i - 1) >> 1;
      if (!less(heap[i]!, heap[p]!)) break;
      [heap[i], heap[p]] = [heap[p]!, heap[i]!];
      i = p;
    }
  };
  const heapPop = (): number[] => {
    const top = heap[0]!;
    const last = heap.pop()!;
    if (heap.length > 0) {
      heap[0] = last;
      for (let i = 0; ; ) {
        let c = 2 * i + 1;
        if (c >= heap.length) break;
        if (c + 1 < heap.length && less(heap[c + 1]!, heap[c]!)) c++;
        if (!less(heap[c]!, heap[i]!)) break;
        [heap[i], heap[c]] = [heap[c]!, heap[i]!];
        i = c;
      }
    }
    return top;
  };

  heapPush([hOf(lv.boxes), 0, 0, 0]);
  let order = 1;
  let expanded = 0;
  while (heap.length > 0 && expanded < GREEDY_EXPANSIONS) {
    const [, , , s] = heapPop()!;
    if (best.get(sKey[s]!) !== s) continue; // stale: a better path to this state was found
    const cur = sBoxes[s]!;
    for (const b of cur) occupied[b] = 1;
    const here = ++stamp;
    {
      let top = 0;
      stack[top++] = sPlayer[s]!;
      seen[sPlayer[s]!] = here;
      while (top > 0) {
        const p = stack[--top]!;
        const q0 = p - w;
        const q1 = p + w;
        const q2 = p - 1;
        const q3 = p + 1;
        if (!wall[q0] && !occupied[q0] && seen[q0] !== here) { seen[q0] = here; stack[top++] = q0; }
        if (!wall[q1] && !occupied[q1] && seen[q1] !== here) { seen[q1] = here; stack[top++] = q1; }
        if (!wall[q2] && !occupied[q2] && seen[q2] !== here) { seen[q2] = here; stack[top++] = q2; }
        if (!wall[q3] && !occupied[q3] && seen[q3] !== here) { seen[q3] = here; stack[top++] = q3; }
      }
    }
    expanded++;
    for (let bi = 0; bi < cur.length; bi++) {
      const b = cur[bi]!;
      for (let k = 0; k < 4; k++) {
        const d = DY[k]! * w + DX[k]!;
        const t = b + d;
        if (seen[b - d] !== here || wall[t] || occupied[t] || !live[t]) continue;
        occupied[b] = 0;
        occupied[t] = 1;
        const frozen = frozenBlock(w, wall, occupied, goal, t);
        let key = '';
        let next: number[] | null = null;
        let nh = 0;
        if (!frozen) {
          next = cur.slice();
          next[bi] = t;
          next.sort((x, y) => x - y);
          nh = hOf(next);
          key = keyOf(next, regionLow(b));
        }
        occupied[t] = 0;
        occupied[b] = 1;
        if (frozen) continue;
        const g = sG[s]! + 1;
        const prev = best.get(key);
        if (prev !== undefined && sG[prev]! <= g) continue;
        const idx = sBoxes.length;
        sBoxes.push(next!);
        sPlayer.push(b);
        sParent.push(s);
        sPushFrom.push(b);
        sPushDir.push(k);
        sG.push(g);
        sKey.push(key);
        best.set(key, idx);
        if (solved(next!)) {
          for (const x of cur) occupied[x] = 0;
          return { pushes: g, moves: reconstruct(w, wall, lv, sParent, sPushFrom, sPushDir, idx) };
        }
        heapPush([nh, g, order++, idx]);
      }
    }
    for (const x of cur) occupied[x] = 0;
  }
  return null;
}

/** The moves for a level in XSB: room-by-room optimal search, with fallbacks; '' when nothing is found. */
function solve(text: string): string {
  const lv = parseLevel(text);
  try {
    const byRooms = solveByRooms(lv);
    if (byRooms !== null) return byRooms.moves;
    const whole = solveWhole(lv);
    if (whole !== null) return whole.moves;
  } catch {
    // A search that throws (e.g. an unreachable walk) falls through to an empty answer.
  }
  return '';
}

for (const id of readdirSync(I).sort()) {
  let moves = '';
  try {
    moves = solve(readFileSync(join(I, id, 'level.txt'), 'utf8'));
  } catch {
    moves = '';
  }
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'solution.txt'), `${moves}\n`);
}

