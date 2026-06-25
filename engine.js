//==ENGINE_START==  (pure logic — no DOM references below this marker, up to ENGINE_END)
var ENGINE = (function () {
  "use strict";

  var SIZE = 8;
  var TILES = ['P','N','B','R','Q','T']; // Pawn, kNight, Bishop, Rook, Queen, Teleport
  // distribution across 64 squares (sums to 64)
  var DISTRIB = { P:16, N:12, B:12, R:12, Q:8, T:4 };
  var TILEVAL = { P:1, N:5, B:4, R:5, Q:8, T:2 };        // material-ish worth of being on a tile
  var TILESTR = { P:1, N:4, B:4, R:4, Q:5, T:1 };        // ordering / teleport-target strength

  var ROOK_DIRS  = [[-1,0],[1,0],[0,-1],[0,1]];
  var BISH_DIRS  = [[-1,-1],[-1,1],[1,-1],[1,1]];
  var QUEEN_DIRS = ROOK_DIRS.concat(BISH_DIRS);
  var KNIGHT_OFF = [[-2,-1],[-2,1],[-1,-2],[-1,2],[1,-2],[1,2],[2,-1],[2,1]];

  function mulberry32(a){
    return function(){
      a |= 0; a = (a + 0x6D2B79F5) | 0;
      var t = Math.imul(a ^ (a >>> 15), 1 | a);
      t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
      return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
    };
  }

  function inB(r,c){ return r>=0 && r<SIZE && c>=0 && c<SIZE; }
  function other(col){ return col === 'w' ? 'b' : 'w'; }

  // ----- board construction -----
  function buildTiles(seed){
    var rng = mulberry32((seed|0) || 1);
    var bag = [];
    for (var k in DISTRIB){ for (var i=0;i<DISTRIB[k];i++) bag.push(k); }
    // Fisher-Yates with seeded rng
    for (var j=bag.length-1;j>0;j--){
      var m = Math.floor(rng()*(j+1));
      var tmp = bag[j]; bag[j]=bag[m]; bag[m]=tmp;
    }
    var t = [];
    for (var r=0;r<SIZE;r++){ t.push([]); for (var c=0;c<SIZE;c++) t[r].push(bag[r*SIZE+c]); }
    return t;
  }

  function emptyGrid(){
    var g=[]; for(var r=0;r<SIZE;r++){ g.push([]); for(var c=0;c<SIZE;c++) g[r].push(null); } return g;
  }

  // pieces are immutable {c:'w'|'b', k:bool}
  function initBoard(seed){
    var tiles = buildTiles(seed);
    var pieces = emptyGrid();
    // Black occupies rows 0,1 (top); White occupies rows 6,7 (bottom). Kings on the back rank.
    for (var c=0;c<SIZE;c++){
      pieces[0][c] = { c:'b', k:false };
      pieces[1][c] = { c:'b', k:false };
      pieces[6][c] = { c:'w', k:false };
      pieces[7][c] = { c:'w', k:false };
    }
    pieces[0][4] = { c:'b', k:true };  // black king
    pieces[7][4] = { c:'w', k:true };  // white king
    return { tiles:tiles, pieces:pieces, turn:'w', winner:null, lastMove:null, seed:(seed|0)||1 };
  }

  function cloneForMove(state){
    // tiles are immutable & shared; clone the pieces grid (rows) only
    var ng = new Array(SIZE);
    for (var r=0;r<SIZE;r++){ ng[r] = state.pieces[r].slice(); }
    return { tiles:state.tiles, pieces:ng, turn:state.turn, winner:state.winner, lastMove:state.lastMove, seed:state.seed };
  }

  function findKing(state, col){
    for (var r=0;r<SIZE;r++) for (var c=0;c<SIZE;c++){
      var p = state.pieces[r][c];
      if (p && p.k && p.c===col) return [r,c];
    }
    return null;
  }

  // ----- move generation for the piece at (r,c) -----
  // forSearch=true caps teleport destinations to keep AI branching sane (full set still used for the human).
  function genMoves(state, r, c, forSearch){
    var p = state.pieces[r][c];
    if (!p) return [];
    var col = p.c;
    var out = [];

    function pushIf(tr,tc, allowCap){
      if (!inB(tr,tc)) return false;
      var q = state.pieces[tr][tc];
      if (!q){ out.push(mk(tr,tc,null)); return true; }          // empty -> can continue sliding
      if (q.c !== col && allowCap !== false){ out.push(mk(tr,tc,q)); }
      return false;                                              // blocked
    }
    function mk(tr,tc,cap){
      return { from:[r,c], to:[tr,tc], capture:!!cap, capturesKing: !!(cap && cap.k), tileFrom: (p.k?'K':state.tiles[r][c]) };
    }
    function slide(dirs){
      for (var d=0; d<dirs.length; d++){
        var tr=r+dirs[d][0], tc=c+dirs[d][1];
        while (inB(tr,tc)){
          var q = state.pieces[tr][tc];
          if (!q){ out.push(mk(tr,tc,null)); }
          else { if (q.c!==col) out.push(mk(tr,tc,q)); break; }
          tr+=dirs[d][0]; tc+=dirs[d][1];
        }
      }
    }

    if (p.k){
      // King ALWAYS moves like a king, ignoring its tile.
      for (var d=0; d<QUEEN_DIRS.length; d++) pushIf(r+QUEEN_DIRS[d][0], c+QUEEN_DIRS[d][1], true);
      return out;
    }

    var tile = state.tiles[r][c];
    switch (tile){
      case 'P': {
        var fwd = (col==='w') ? -1 : 1;                 // white moves up (toward row 0)
        // forward one (only into empty)
        if (inB(r+fwd,c) && !state.pieces[r+fwd][c]) out.push(mk(r+fwd,c,null));
        // diagonal captures only
        for (var dc=-1; dc<=1; dc+=2){
          var tr=r+fwd, tc=c+dc;
          if (inB(tr,tc)){ var q=state.pieces[tr][tc]; if (q && q.c!==col) out.push(mk(tr,tc,q)); }
        }
        break;
      }
      case 'N': {
        for (var i=0;i<KNIGHT_OFF.length;i++) pushIf(r+KNIGHT_OFF[i][0], c+KNIGHT_OFF[i][1], true);
        break;
      }
      case 'B': slide(BISH_DIRS); break;
      case 'R': slide(ROOK_DIRS); break;
      case 'Q': slide(QUEEN_DIRS); break;
      case 'T': {
        // teleport to ANY empty square (cannot capture)
        var dests = [];
        for (var tr2=0;tr2<SIZE;tr2++) for (var tc2=0;tc2<SIZE;tc2++){
          if (!state.pieces[tr2][tc2] && !(tr2===r && tc2===c)) dests.push([tr2,tc2]);
        }
        if (forSearch && dests.length > 8){
          var ek = findKing(state, other(col));
          dests.sort(function(a,b){ return tscore(b)-tscore(a); });
          function tscore(d){
            var s = TILESTR[state.tiles[d[0]][d[1]]] || 0;
            if (ek){ s += (7 - Math.max(Math.abs(d[0]-ek[0]), Math.abs(d[1]-ek[1]))); }
            return s;
          }
          dests = dests.slice(0,8);
        }
        for (var z=0; z<dests.length; z++) out.push(mk(dests[z][0], dests[z][1], null));
        break;
      }
    }
    return out;
  }

  function allMoves(state, col, forSearch){
    var moves = [];
    for (var r=0;r<SIZE;r++) for (var c=0;c<SIZE;c++){
      var p = state.pieces[r][c];
      if (p && p.c===col){
        var ms = genMoves(state, r, c, forSearch);
        for (var i=0;i<ms.length;i++) moves.push(ms[i]);
      }
    }
    return moves;
  }

  function applyMove(state, m){
    var ns = cloneForMove(state);
    var fr=m.from, to=m.to;
    var moving = ns.pieces[fr[0]][fr[1]];
    var target = ns.pieces[to[0]][to[1]];
    ns.pieces[to[0]][to[1]] = moving;
    ns.pieces[fr[0]][fr[1]] = null;
    if (target && target.k){ ns.winner = moving.c; }   // captured a king -> win
    ns.lastMove = { from:fr.slice(), to:to.slice() };
    ns.turn = other(state.turn);
    return ns;
  }

  // ----- evaluation (from `col` perspective) -----
  function evaluate(state, col){
    if (state.winner){
      if (state.winner === 'draw') return 0;
      return state.winner === col ? 1000000 : -1000000;
    }
    var score = 0;
    var myKing=null, opKing=null;
    var r,c,p;
    for (r=0;r<SIZE;r++) for (c=0;c<SIZE;c++){
      p = state.pieces[r][c];
      if (!p) continue;
      if (p.k){ if (p.c===col) myKing=[r,c]; else opKing=[r,c]; continue; }
      var v = 100 + (TILEVAL[state.tiles[r][c]] || 0);
      score += (p.c===col) ? v : -v;
    }
    // king pressure: reward own pieces crowding the enemy king, punish the reverse
    for (r=0;r<SIZE;r++) for (c=0;c<SIZE;c++){
      p = state.pieces[r][c];
      if (!p || p.k) continue;
      var enemyK = (p.c===col) ? opKing : myKing;
      if (!enemyK) continue;
      var dist = Math.max(Math.abs(r-enemyK[0]), Math.abs(c-enemyK[1]));
      var press = Math.max(0, 7 - dist) * 0.8;
      score += (p.c===col) ? press : -press;
    }
    return score;
  }

  // ----- search (negamax + alpha-beta + iterative deepening) -----
  function orderMoves(state, moves){
    for (var i=0;i<moves.length;i++){
      var m = moves[i];
      var s = 0;
      if (m.capturesKing) s = 1e6;
      else if (m.capture) s = 1000 + (TILESTR[state.tiles[m.to[0]][m.to[1]]]||0);
      else s = (TILESTR[state.tiles[m.to[0]][m.to[1]]]||0);
      m._o = s;
    }
    moves.sort(function(a,b){ return b._o - a._o; });
    return moves;
  }

  function negamax(state, depth, alpha, beta, col, ctx, ply){
    if (state.winner){
      if (state.winner === 'draw') return 0;
      // prefer faster wins / slower losses
      return state.winner === col ? (1000000 - ply) : -(1000000 - ply);
    }
    if (depth === 0) return evaluate(state, col);
    ctx.nodes++;
    if (ctx.nodes > ctx.maxNodes || now() > ctx.deadline){ ctx.aborted = true; return evaluate(state, col); }

    var moves = orderMoves(state, allMoves(state, col, true));
    if (moves.length === 0) return 0; // no moves -> treat as draw within search
    var best = -Infinity;
    for (var i=0;i<moves.length;i++){
      var child = applyMove(state, moves[i]);
      var val = -negamax(child, depth-1, -beta, -alpha, other(col), ctx, ply+1);
      if (ctx.aborted) return best > -Infinity ? best : val;
      if (val > best) best = val;
      if (val > alpha) alpha = val;
      if (alpha >= beta) break;
    }
    return best;
  }

  function rootSearch(state, col, depth, ctx){
    var moves = orderMoves(state, allMoves(state, col, true));
    if (moves.length === 0) return { move:null, score:0, scored:[] };
    var alpha=-Infinity, beta=Infinity, best=-Infinity, bestMove=moves[0];
    var scored=[];
    for (var i=0;i<moves.length;i++){
      var child = applyMove(state, moves[i]);
      var val = -negamax(child, depth-1, -beta, -alpha, other(col), ctx, 1);
      if (ctx.aborted){ if (scored.length===0) scored.push({move:moves[i],score:val}); break; }
      scored.push({ move:moves[i], score:val });
      if (val > best){ best = val; bestMove = moves[i]; }
      if (val > alpha) alpha = val;
    }
    return { move:bestMove, score:best, scored:scored };
  }

  var _now = (typeof performance!=='undefined' && performance.now) ? function(){return performance.now();} : function(){return +new Date();};
  function now(){ return _now(); }

  // deterministic flag for tests (no random tie-break)
  var DETERMINISTIC = false;
  var _airng = Math.random;

  function chooseAIMove(state, difficulty){
    var col = state.turn;
    var legal = allMoves(state, col, false);
    if (legal.length === 0) return null;

    // 1) take an immediate king capture if available (instant win)
    for (var i=0;i<legal.length;i++) if (legal[i].capturesKing) return legal[i];

    var maxDepth = difficulty==='easy' ? 1 : (difficulty==='hard' ? 3 : 2);
    var budget   = difficulty==='hard' ? 1500 : (difficulty==='easy' ? 250 : 700);
    var ctx = { nodes:0, maxNodes: difficulty==='hard'?260000:90000, deadline: now()+budget, aborted:false };

    var chosen = legal[0], lastScored = null;
    for (var d=1; d<=maxDepth; d++){
      ctx.aborted = false;
      var res = rootSearch(state, col, d, ctx);
      if (res.move){ chosen = res.move; lastScored = res.scored; }
      if (ctx.aborted) break;
    }

    // 2) safety: avoid handing the opponent an immediate king-capture, if a safe move exists
    //    (covers easy/shallow searches and time-outs)
    var safe = filterKingSafe(state, lastScored ? lastScored.map(function(s){return s.move;}) : legal, col);
    if (safe.length){
      // among safe moves keep those near the best score
      if (lastScored){
        var sset = new Set(safe);
        var pool = lastScored.filter(function(s){ return sset.has(s.move); });
        if (pool.length){
          pool.sort(function(a,b){ return b.score-a.score; });
          var top = pool[0].score;
          var near = pool.filter(function(s){ return s.score >= top - 1.0; });
          chosen = pickFrom(near.map(function(s){return s.move;}), difficulty);
        } else {
          chosen = pickFrom(safe, difficulty);
        }
      } else {
        chosen = pickFrom(safe, difficulty);
      }
    }
    return chosen;
  }

  function filterKingSafe(state, moves, col){
    var safe = [];
    for (var i=0;i<moves.length;i++){
      var child = applyMove(state, moves[i]);
      if (child.winner === col) { safe.push(moves[i]); continue; } // winning move is "safe"
      // does opponent have an immediate king capture in reply?
      var opp = allMoves(child, other(col), true);
      var hangs = false;
      for (var j=0;j<opp.length;j++){ if (opp[j].capturesKing){ hangs = true; break; } }
      if (!hangs) safe.push(moves[i]);
    }
    return safe;
  }

  function pickFrom(moves, difficulty){
    if (!moves.length) return null;
    if (DETERMINISTIC) return moves[0];
    if (difficulty==='hard') return moves[0];
    // a little variety for easy/medium
    var n = difficulty==='easy' ? moves.length : Math.min(moves.length, 3);
    return moves[Math.floor(_airng()*n)];
  }

  return {
    SIZE:SIZE, TILES:TILES, DISTRIB:DISTRIB,
    mulberry32:mulberry32, inB:inB, other:other,
    initBoard:initBoard, buildTiles:buildTiles,
    genMoves:genMoves, allMoves:allMoves, applyMove:applyMove,
    evaluate:evaluate, findKing:findKing,
    chooseAIMove:chooseAIMove, filterKingSafe:filterKingSafe,
    setDeterministic:function(v){ DETERMINISTIC=!!v; },
    setAIRandom:function(fn){ _airng = fn || Math.random; }
  };
})();

module.exports = ENGINE;
