import fs from'node:fs';
const I=process.env.MAKEFUN_INPUT_DIR??'/input',O=process.env.MAKEFUN_OUTPUT_DIR??'/output';
const X=[0,0,-1,1],Y=[-1,1,0,0],S=['u','d','l','r'],SC=(a:number,b:number)=>a-b;
let RS=0;
function BF(w:number,A:Uint8Array,G:number[],d:number){const r:any=d?new Int32Array(A.length).fill(-1):new Uint8Array(A.length),q=[...G],D=[-w,w,-1,1];for(const g of G)r[g]=d?0:1;for(let i=0;i<q.length;i++){const x=q[i];for(const e of D){const y=x-e;if(y<0||y>=A.length||A[y]||A[y-e]||(d?r[y]>-1:r[y]))continue;r[y]=d?r[x]+1:1;q.push(y);}}return r;}
function RG(w:number,A:Uint8Array,C:Uint8Array,N:Int32Array,T:Int32Array,f:number){const s=++RS,D=[-w,w,-1,1];let l=f,t=0;T[t++]=f;N[f]=s;while(t>0){const p=T[--t];if(p<l)l=p;for(const e of D){const q=p+e;if(!A[q]&&!C[q]&&N[q]!==s){N[q]=s;T[t++]=q;}}}return l;}
function MK(w:number,A:Uint8Array,C:Uint8Array,N:Int32Array,T:Int32Array,f:number,h:number){const D=[-w,w,-1,1];let t=0;T[t++]=f;N[f]=h;while(t>0){const p=T[--t];for(const e of D){const q=p+e;if(!A[q]&&!C[q]&&N[q]!==h){N[q]=h;T[t++]=q;}}}}
function FB(w:number,A:Uint8Array,C:Uint8Array,g:Uint8Array,t:number){for(const a of[t,t-1,t-w,t-w-1]){const b=a+1,c=a+w,d=c+1;if(a<0||d>=A.length)continue;if((A[a]||C[a])&&(A[b]||C[b])&&(A[c]||C[c])&&(A[d]||C[d])&&((C[a]&&!g[a])||(C[b]&&!g[b])||(C[c]&&!g[c])||(C[d]&&!g[d])))return true;}return false;}
const LS=(a:number[],b:number[])=>a[0]!=b[0]?a[0]<b[0]:a[1]!=b[1]?a[1]<b[1]:a[2]<b[2];
function HP(h:number[][],e:number[]){let i=h.length;h.push(e);while(i>0){const p=(i-1)>>1;if(!LS(h[i]!,h[p]!))break;[h[i],h[p]]=[h[p],h[i]];i=p;}}
function HQ(h:number[][]){const t=h[0]!,l=h.pop()!;if(h.length){h[0]=l;for(let i=0;;){let c=2*i+1;if(c>=h.length)break;if(c+1<h.length&&LS(h[c+1]!,h[c]!))c++;if(!LS(h[c]!,h[i]!))break;[h[i],h[c]]=[h[c],h[i]];i=c;}}return t;}
const PK=(b:number[])=>b.reduceRight((p,x)=>p*256+x,255);
const CL=(o:Uint8Array,c:number[])=>{for(const x of c)o[x]=0;};
function WK(w:number,A:Uint8Array,B:number[],f:number,t:number){if(f===t)return'';const C=new Uint8Array(A.length);for(const b of B)C[b]=1;const P=new Int32Array(A.length).fill(-1),H=new Uint8Array(A.length),q=[f];P[f]=f;for(let i=0;i<q.length;i++){const p=q[i]!;if(p===t)break;for(let k=0;k<4;k++){const z=p+Y[k]!*w+X[k]!;if(A[z]||C[z]||P[z]!==-1)continue;P[z]=p;H[z]=k;q.push(z);}}if(P[t]===-1)throw 0;let s='';for(let p=t;p!==f;p=P[p]!)s=S[H[p]!]!+s;return s;}
function PL(P:number[],s:number){let n=0;for(;s>0;s=P[s]!)n++;return n;}function RC(w:number,A:Uint8Array,v:any,P:number[],F:number[],D:number[],f:number){const p:number[]=[];for(let s=f;s>0;s=P[s]!)p.push(s);p.reverse();let m='',pl=v.player,bx=v.boxes.slice();for(const s of p){const fr=F[s]!,k=D[s]!,d=Y[k]!*w+X[k]!;m+=WK(w,A,bx,pl,fr-d);m+=S[k]!.toUpperCase();pl=fr;bx[bx.indexOf(fr)]=fr+d;bx.sort(SC);}return m;}
function PS(t:string):any{const r=t.split('\n').filter(x=>x.length),h=r.length,w=Math.max(...r.map(x=>x.length)),A=new Uint8Array(w*h).fill(1),G:number[]=[],B:number[]=[];let p=-1;r.forEach((row,y)=>{for(let x=0;x<row.length;x++){const c=row[x]!,i=y*w+x;if(c=='#')continue;A[i]=0;if(c=='.'||c=='*'||c=='+')G.push(i);if(c=='$'||c=='*')B.push(i);if(c=='@'||c=='+')p=i;}});for(let y=0;y<h;y++)for(let x=0;x<w;x++)if(!x||!y||x==w-1||y==h-1)A[y*w+x]=1;B.sort(SC);G.sort(SC);return{w,h,wall:A,goals:G,boxes:B,player:p};}
function SR(v:any,mx:number,md:number):any{
 const{w,wall,goals}=v,z=wall.length,n=v.boxes.length;
 const go=new Uint8Array(z);for(const g of goals)go[g]=1;
 const li=BF(w,wall,goals,0),di=BF(w,wall,goals,1);
 if(v.boxes.some(b=>!li[b]||(md&&di[b]<0)))return null;
 const sv=(b:number[])=>b.every(x=>go[x]);
 if(sv(v.boxes))return{pushes:0,moves:''};
 const hf=(b:number[])=>{let h=0;for(const x of b)h+=di[x];return h;};
 const oc=new Uint8Array(z),sn=new Int32Array(z),sr=new Int32Array(z),st=new Int32Array(z);
 let sp=0;
 const B=[PK(v.boxes)],P=[v.player],Q=[-1],F=[-1],D=[-1],G=[0],K:number[]=[],BT=new Map<number,number>();
 for(const b of v.boxes)oc[b]=1;
 const k0=PK(v.boxes)*256+RG(w,wall,oc,sr,st,v.player);
 K.push(k0);BT.set(k0,0);
 for(const b of v.boxes)oc[b]=0;
 const hp:number[][]=[];
 if(md){const h0=hf(v.boxes);HP(hp,[h0,md==1?h0:0,0,0]);}
 let od=1,ex=0,hd=0,fd=-1;
 const cur=new Array<number>(n);
 while(md?hp.length>0&&ex<mx:hd<B.length&&fd<0){
  let s:number;
  if(md){s=HQ(hp)![3]!;if(BT.get(K[s]!)!==s)continue;}
  else s=hd++;
  for(let i=0,q=B[s]!;i<n;i++){cur[i]=q&255;q>>>=8;}
  if(md==1&&sv(cur))return{pushes:G[s]!,moves:RC(w,wall,v,Q,F,D,s)};
  for(const b of cur)oc[b]=1;
  const hr=++sp;MK(w,wall,oc,sn,st,P[s]!,hr);
  if(md)ex++;
  for(let bi=0;bi<n;bi++){
   const b=cur[bi]!;
   for(let k=0;k<4;k++){
    const d=Y[k]!*w+X[k]!,t=b+d;
    if(sn[b-d]!==hr||wall[t]||oc[t]||!li[t])continue;
    oc[b]=0;oc[t]=1;
    const fr=FB(w,wall,oc,go,t);
    let key=-1,nx=-1,nh=0;
    if(!fr){const nb=cur.slice();nb[bi]=t;nb.sort(SC);nx=PK(nb);nh=md?hf(nb):0;key=nx*256+RG(w,wall,oc,sr,st,b);}
    oc[t]=0;oc[b]=1;
    if(fr)continue;
    let g=0;
    if(md){g=G[s]!+1;const pv=BT.get(key);if(pv!==undefined&&G[pv]!<=g)continue;}
    else{if(BT.has(key))continue;if(B.length>=mx){CL(oc,cur);return null;}}
    const ix=B.length;
    B.push(nx);P.push(b);Q.push(s);F.push(b);D.push(k);G.push(g);K.push(key);BT.set(key,ix);
    if(md==2&&sv(cur.map((x,i)=>i==bi?t:x))){CL(oc,cur);return{pushes:g,moves:RC(w,wall,v,Q,F,D,ix)};}
    if(md)HP(hp,[md==1?g+nh:nh,md==1?nh:g,od++,ix]);
    else if(sv(cur.map((x,i)=>i==bi?t:x))){fd=ix;break;}
   }
   if(fd>=0)break;
  }
  CL(oc,cur);
 }
 if(!md&&fd>=0)return{pushes:PL(Q,fd),moves:RC(w,wall,v,Q,F,D,fd)};
 return null;
}
function RM(v:any){const{w,wall,goals,boxes,player}=v,li=BF(w,wall,goals,0),row=Math.floor(player/w),ct=new Uint8Array(wall.length);for(let x=0;x<w;x++){const i=row*w+x;if(!wall[i]&&!li[i])ct[i]=1;}if(boxes.some(b=>ct[b]))return null;const pt=new Int32Array(wall.length).fill(-1),R:any[]=[];for(let s=0;s<wall.length;s++){if(wall[s]||ct[s]||pt[s]>=0)continue;const q=[s];pt[s]=R.length;for(let i=0;i<q.length;i++){const p=q[i]!;for(let k=0;k<4;k++){const z=p+Y[k]!*w+X[k]!;if(!wall[z]&&!ct[z]&&pt[z]<0){pt[z]=R.length;q.push(z);}}}R.push({boxes:[],goals:[]});}for(const b of boxes){if(pt[b]<0)return null;R[pt[b]!]!.boxes.push(b);}for(const g of goals){if(pt[g]<0)return null;R[pt[g]!]!.goals.push(g);}if(R.some(r=>r.boxes.length!==r.goals.length))return null;return R.filter(r=>r.boxes.length>0);}
const SM=(v:any):any=>SR(v,25e4,0)??SR(v,1e6,0)??SR(v,4e5,1)??SR(v,4e5,2);
function BR(v:any):any{const R=RM(v);if(!R)return null;let pl=v.player,ps=0,m='';const dn=new Set<number>();for(let r=0;r<R.length;r++){const A=v.wall.slice();for(let o=0;o<R.length;o++){if(o===r)continue;const s=dn.has(o)?R[o]!.goals:R[o]!.boxes;for(const b of s)A[b]=1;}const u:any={w:v.w,h:v.h,wall:A,goals:R[r]!.goals.slice().sort(SC),boxes:R[r]!.boxes.slice().sort(SC),player:pl};const s=SM(u);if(!s)return null;ps+=s.pushes;m+=s.moves;for(const c of s.moves.toLowerCase())pl+=c=='u'?-v.w:c=='d'?v.w:c=='l'?-1:1;dn.add(r);}return{pushes:ps,moves:m};}
function Z(t:string){const v=PS(t);try{const a=BR(v);return a?a.moves:'';}catch{return '';}}
for(const id of fs.readdirSync(I).sort()){let m='';try{m=Z(fs.readFileSync(I+'/'+id+'/level.txt','utf8'));}catch{m='';}fs.mkdirSync(O+'/'+id,{recursive:true});fs.writeFileSync(O+'/'+id+'/solution.txt',m+'\n');}
