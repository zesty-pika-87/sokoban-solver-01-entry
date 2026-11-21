// Room-wise push-optimal Sokoban solver: A* per room on the whole board, other rooms' boxes as walls.
// Deterministic: fixed orders, work budgets, no clock.
import {mkdirSync,readdirSync,readFileSync,writeFileSync} from 'node:fs';
const I=process.env.MAKEFUN_INPUT_DIR??'/input',O=process.env.MAKEFUN_OUTPUT_DIR??'/output',L='udlr';
const solve=t=>{
  const r=t.split('\n');
  while(r.length&&!r[r.length-1])r.pop();
  const W=Math.max(...r.map(s=>s.length)),g=[];
  for(const s of r)for(let x=0;x<W;x++)g.push(s[x]||'#');
  const S=g.length,D=[-W,W,-1,1],wall=i=>i<0||i>=S||g[i]==='#';
  let H=0,P=0;
  for(let i=0;i<S;i++)if(g[i]==='@'||g[i]==='+'){H=(i/W)|0;P=i}
  const bfs=(a,ok)=>{const d=new Map([[a,0]]),q=[a];for(let h=0;h<q.length;h++){const c=q[h];for(let k=0;k<4;k++){const n=c+D[k];if(ok(n)&&!d.has(n)){d.set(n,d.get(c)+1);q.push(n)}}}return d};
  const walk=(a,b,ok)=>{const d=bfs(b,ok);if(!d.has(a))return null;let s='',x=a;while(x!==b){for(let k=0;k<4;k++){const n=x+D[k];if(d.get(n)===d.get(x)-1){s+=L[k];x=n;break}}}return s};
  const seen=new Uint8Array(S),R=[];
  for(let i=0;i<S;i++){
    if(wall(i)||(i/W|0)===H||seen[i])continue;
    const c=[],q=[i];seen[i]=1;
    while(q.length){const x=q.pop();c.push(x);
      for(let k=0;k<4;k++){const n=x+D[k];
        if((n/W|0)!==H&&!wall(n)&&!seen[n]){seen[n]=1;q.push(n)}}}
    const B=[],G=[];
    for(const x of c){if(g[x]==='$'||g[x]==='*')B.push(x);if(g[x]==='.'||g[x]==='*'||g[x]==='+')G.push(x)}
    R.push({B:B.sort((a,b)=>a-b),G,done:false});
  }
  let p=P,out='';
  for(const rm of R){
    const O2=new Set();
    for(const o of R)if(o!==rm)for(const b of o.done?o.G:o.B)O2.add(b);
    const ok=i=>!wall(i)&&!O2.has(i);
    const B=[...rm.B],G=rm.G,n=B.length;
    const dist=G.map(g0=>bfs(g0,ok));
    const live=new Set(G),lq=[...G];
    for(let h=0;h<lq.length;h++){const c=lq[h];for(let k=0;k<4;k++){const nn=c-D[k],o=nn-D[k];if(ok(nn)&&ok(o)&&!live.has(nn)){live.add(nn);lq.push(nn)}}}
    const heur=b=>{let m=1e9;const f=(i,u,s)=>{if(s<m){if(i===n)m=s;else for(let j=0;j<n;j++)if(!(u>>j&1)){const dd=dist[j].get(b[i]);if(dd!==undefined)f(i+1,u|1<<j,s+dd)}}};f(0,0,0);return m};
    const key=(b,pp)=>b.reduce((k,x)=>k*S+x,pp);
    let mn=0,qn=0;const Bk=[];
    const push=e=>{(Bk[e[0]]=Bk[e[0]]||[]).push(e);if(e[0]<mn)mn=e[0];qn++};
    const pop=()=>{while(!Bk[mn]||!Bk[mn].length)mn++;qn--;return Bk[mn].pop()};
    const st={b:B,p:p,g:0,par:null,mv:null,k:key(B,p)};
    const best=new Map([[st.k,0]]);
    push([heur(st.b),st]);
    let ex=0,sl=null;
    while(qn>0){
      const cur=pop()[1];
      if(cur.g>best.get(cur.k))continue;
      if(cur.b.every(x=>G.includes(x))){
        const ps=[];let nn=cur;while(nn.mv){ps.push(nn.mv);nn=nn.par}ps.reverse();
        let pp=p,bs=[...B],mv='';
        for(const [bx,di] of ps){
          const s=bx-D[di],tt=bx+D[di];
          const w=walk(pp,s,x=>ok(x)&&!bs.includes(x));
          if(w===null){mv=null;break}
          mv+=w+L[di];
          bs=bs.map(x=>x===bx?tt:x).sort((a,b)=>a-b);pp=bx;
        }
        if(mv!==null){sl={moves:mv,end:pp};break}
        continue;
      }
      if(++ex>200000)break;
      const rg=bfs(cur.p,x=>ok(x)&&!cur.b.includes(x));
      for(let bi=0;bi<n;bi++){const bx=cur.b[bi];
        for(let d=0;d<4;d++){
          const s=bx-D[d],tt=bx+D[d];
          if(!ok(s)||!ok(tt)||cur.b.includes(tt)||!rg.has(s)||!live.has(tt))continue;
          const nb=[...cur.b];nb[bi]=tt;nb.sort((a,b)=>a-b);
          const ng=cur.g+1,nd={b:nb,p:bx,g:ng,par:cur,mv:[bx,d],k:key(nb,bx)};
          if(best.has(nd.k)&&best.get(nd.k)<=ng)continue;
          best.set(nd.k,ng);
          const hh=heur(nb);
          if(hh<1e9)push([ng+hh,nd]);
        }}
    }
    if(!sl)return'';
    out+=sl.moves;p=sl.end;rm.done=true;
  }
  return out;
};
for(const id of readdirSync(I).sort()){
  const m=solve(readFileSync(I+'/'+id+'/level.txt','utf8'));
  mkdirSync(O+'/'+id,{recursive:true});
  writeFileSync(O+'/'+id+'/solution.txt',m+'\n');
}
