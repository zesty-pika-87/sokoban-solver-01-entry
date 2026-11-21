// Room-wise push-optimal Sokoban solver: a level splits into independent rooms off one hallway;
// each room is solved push-optimally with A* (admissible box-goal assignment heuristic,
// dead-square + frozen-2x2 pruning, player-region state keys) on the whole board, the other
// rooms' boxes standing as walls, then the room solutions are stitched in door order.
// Deterministic: fixed orders, work-based budgets, no clock.
import {mkdirSync,readdirSync,readFileSync,writeFileSync} from 'node:fs';
import {join} from 'node:path';
const I=process.env.MAKEFUN_INPUT_DIR??'/input',O=process.env.MAKEFUN_OUTPUT_DIR??'/output';
const DX=[0,0,-1,1],DY=[-1,1,0,0],L='udlr';
const perms=n=>{const r=[],f=(a,b)=>{if(!b.length)r.push(a);else for(let i=0;i<b.length;i++)f([...a,b[i]],b.filter((_,j)=>j!==i))};f([],Array.from({length:n},(_,i)=>i));return r};
const solve=txt=>{
  const rows=txt.split('\n');
  while(rows.length&&rows[rows.length-1]==='')rows.pop();
  const W=Math.max(...rows.map(r=>r.length));
  const g=[];
  for(const r of rows)for(let x=0;x<W;x++)g.push(r[x]||'#');
  const wall=i=>i<0||i>=g.length||g[i]==='#';
  let hy=0,px=0;
  for(let i=0;i<g.length;i++)if(g[i]==='@'||g[i]==='+'){hy=(i/W)|0;px=i}
  const flood=(a,ok)=>{const s=new Set([a]),q=[a];while(q.length){const c=q.shift();for(let d=0;d<4;d++){const n=c+DX[d]+DY[d]*W;if(ok(n)&&!s.has(n)){s.add(n);q.push(n)}}}return s};
  const path=(a,b,ok)=>{if(a===b)return'';const par=new Map([[a,-1]]),q=[a];while(q.length){const c=q.shift();for(let d=0;d<4;d++){const n=c+DX[d]+DY[d]*W;if(ok(n)&&!par.has(n)){par.set(n,c*4+d);if(n===b){let s='',x=b;while(x!==a){const v=par.get(x);s=L[v%4]+s;x=(v/4)|0}return s}q.push(n)}}}return null};
  const seen=new Uint8Array(g.length),rooms=[];
  for(let i=0;i<g.length;i++){
    if(wall(i)||(i/W|0)===hy||seen[i])continue;
    const cells=[],q=[i];seen[i]=1;let door=-1;
    while(q.length){const c=q.pop();cells.push(c);
      for(let d=0;d<4;d++){const n=c+DX[d]+DY[d]*W;
        if((n/W|0)===hy){if(!wall(n))door=c;continue}
        if(!wall(n)&&!seen[n]){seen[n]=1;q.push(n)}}}
    const boxes=[],goals=[];
    for(const c of cells){if(g[c]==='$'||g[c]==='*')boxes.push(c);if(g[c]==='.'||g[c]==='*'||g[c]==='+')goals.push(c)}
    rooms.push({cells,door,boxes:boxes.sort((a,b)=>a-b),goals,done:false});
  }
  rooms.sort((a,b)=>a.door%W-b.door%W);
  let p=px,out='';
  for(const rm of rooms){
    const other=new Set();
    for(const o of rooms)if(o!==rm)for(const b of o.done?o.goals:o.boxes)other.add(b);
    const ok=i=>!wall(i)&&!other.has(i);
    const boxes=[...rm.boxes],goals=rm.goals,nB=boxes.length,goalSet=new Set(goals);
    const dist=goals.map(g0=>{const d=new Map([[g0,0]]),q=[g0];while(q.length){const c=q.shift();for(let d2=0;d2<4;d2++){const n=c+DX[d2]+DY[d2]*W;if(ok(n)&&!d.has(n)){d.set(n,d.get(c)+1);q.push(n)}}}return d});
    const live=new Set(goals),lq=[...goals];
    while(lq.length){const c=lq.shift();for(let d=0;d<4;d++){const n=c-DX[d]-DY[d]*W,o=n-DX[d]-DY[d]*W;if(ok(n)&&ok(o)&&!live.has(n)){live.add(n);lq.push(n)}}}
    const pm=perms(nB);
    const heur=b=>{let m=1e9;for(const pp of pm){let s=0;for(let i=0;i<nB;i++){const dd=dist[pp[i]].get(b[i]);if(dd===undefined){s=1e9;break}s+=dd}if(s<m)m=s}return m};
    const bsOf=b=>new Set(b);
    const regMin=(pp,b)=>{const s=flood(pp,n=>ok(n)&&!b.has(n));let m=1e9;for(const x of s)if(x<m)m=x;return m};
    const key=(b,pp)=>b.join(',')+'|'+regMin(pp,bsOf(b));
    const heap=[];let tie=0;
    const cmp=(a,b)=>a[0]-b[0]||a[1]-b[1];
    const hpush=e=>{heap.push(e);let i=heap.length-1;while(i>0){const j=(i-1)>>1;if(cmp(heap[j],e)<=0)break;heap[i]=heap[j];i=j}heap[i]=e};
    const hpop=()=>{const t=heap[0],l=heap.pop();if(heap.length){let i=0;for(;;){const a=2*i+1,b2=a+1;if(a>=heap.length)break;let m=a;if(b2<heap.length&&cmp(heap[b2],heap[a])<0)m=b2;if(cmp(l,heap[m])<=0)break;heap[i]=heap[m];i=m}heap[i]=l}return t};
    const start={b:boxes,p:p,g:0,par:null,mv:null,k:''};
    start.k=key(start.b,start.p);
    const best=new Map([[start.k,0]]);
    hpush([heur(start.b),tie++,start]);
    let exp=0,solved=null;
    while(heap.length){
      const cur=hpop()[2];
      if(cur.g>best.get(cur.k))continue;
      if(cur.b.every(x=>goalSet.has(x))){
        const ps=[];let n=cur;while(n.mv){ps.push(n.mv);n=n.par}ps.reverse();
        let pp=p,bs=[...boxes],mv='';
        for(const [bx,di] of ps){
          const s=bx-DX[di]-DY[di]*W,t=bx+DX[di]+DY[di]*W;
          const bss=bsOf(bs);
          const w=path(pp,s,n=>ok(n)&&!bss.has(n));
          if(w===null){mv=null;break}
          mv+=w+L[di];
          bs=bs.map(x=>x===bx?t:x).sort((a,b)=>a-b);pp=bx;
        }
        if(mv!==null){solved={moves:mv,end:pp};break}
        continue;
      }
      if(++exp>200000)break;
      const bs=bsOf(cur.b),reg=flood(cur.p,n=>ok(n)&&!bs.has(n));
      for(let bi=0;bi<nB;bi++){const bx=cur.b[bi];
        for(let d=0;d<4;d++){
          const s=bx-DX[d]-DY[d]*W,t=bx+DX[d]+DY[d]*W;
          if(!ok(s)||!ok(t)||bs.has(t)||!reg.has(s)||!live.has(t))continue;
          const nb=[...cur.b];nb[bi]=t;nb.sort((a,b)=>a-b);
          const nbs=new Set(nb);let dead=false;
          for(const a of [t,t-1,t-W,t-W-1]){
            const cc=[a,a+1,a+W,a+W+1];let all=true;
            for(const c of cc)if(!wall(c)&&!other.has(c)&&!nbs.has(c)){all=false;break}
            if(all&&cc.some(c=>nbs.has(c)&&!goalSet.has(c))){dead=true;break}
          }
          if(dead)continue;
          const ng=cur.g+1,nd={b:nb,p:bx,g:ng,par:cur,mv:[bx,d],k:''};
          nd.k=key(nb,bx);
          if(best.has(nd.k)&&best.get(nd.k)<=ng)continue;
          best.set(nd.k,ng);
          hpush([ng+heur(nb),tie++,nd]);
        }}
    }
    if(!solved)return'';
    out+=solved.moves;p=solved.end;rm.done=true;
  }
  return out;
};
for(const id of readdirSync(I).sort()){
  const moves=solve(readFileSync(join(I,id,'level.txt'),'utf8'));
  mkdirSync(join(O,id),{recursive:true});
  writeFileSync(join(O,id,'solution.txt'),moves+'\n');
}
