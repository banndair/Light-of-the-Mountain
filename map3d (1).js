/* Light of the Mountain – map3d.js
   3D-Lowpoly-Karte (WebGL). Wird von index.html benutzt; fällt das nicht, bleibt die alte 2D-Karte. */
(function(){
'use strict';
const PI=Math.PI,cl=(v,a,b)=>Math.max(a,Math.min(b,v)),sm=(a,b,x)=>{const t=cl((x-a)/(b-a),0,1);return t*t*(3-2*t);};
const hxc={};const hx=s=>hxc[s]||(hxc[s]=[parseInt(s.substr(1,2),16)/255,parseInt(s.substr(3,2),16)/255,parseInt(s.substr(5,2),16)/255]);
const mixc=(a,b,t)=>[a[0]+(b[0]-a[0])*t,a[1]+(b[1]-a[1])*t,a[2]+(b[2]-a[2])*t];
const hs=(x,y)=>{const h=Math.sin(x*127.1+y*311.7)*43758.5453;return h-Math.floor(h);};
const vn=(x,y)=>{const xi=Math.floor(x),yi=Math.floor(y),xf=x-xi,yf=y-yi,u=xf*xf*(3-2*xf),v=yf*yf*(3-2*yf);return(hs(xi,yi)*(1-u)+hs(xi+1,yi)*u)*(1-v)+(hs(xi,yi+1)*(1-u)+hs(xi+1,yi+1)*u)*v;};
const fbm=(x,y)=>(vn(x,y)*.6+vn(x*2.1,y*2.1)*.3+vn(x*4.3,y*4.3)*.1)*2-1;
let seed=12345;const rnd=()=>{seed|=0;seed=seed+0x6D2B79F5|0;let t=Math.imul(seed^seed>>>15,1|seed);t=t+Math.imul(t^t>>>7,61|t)^t;return((t^t>>>14)>>>0)/4294967296;};
/* ---------- Matrizen (spaltenweise) ---------- */
const M4={
 id:()=>[1,0,0,0,0,1,0,0,0,0,1,0,0,0,0,1],
 mul(a,b){const o=new Array(16);for(let c=0;c<4;c++)for(let r=0;r<4;r++){let s=0;for(let k=0;k<4;k++)s+=a[k*4+r]*b[c*4+k];o[c*4+r]=s;}return o;},
 persp(f,asp,n,fa){const t=1/Math.tan(f/2);return[t/asp,0,0,0,0,t,0,0,0,0,(fa+n)/(n-fa),-1,0,0,2*fa*n/(n-fa),0];},
 look(e,c){let z=[e[0]-c[0],e[1]-c[1],e[2]-c[2]];let l=Math.hypot(...z);z=z.map(v=>v/l);let x=[z[2],0,-z[0]];l=Math.hypot(...x);x=x.map(v=>v/l);const y=[z[1]*x[2]-z[2]*x[1],z[2]*x[0]-z[0]*x[2],z[0]*x[1]-z[1]*x[0]];
  return[x[0],y[0],z[0],0,x[1],y[1],z[1],0,x[2],y[2],z[2],0,-(x[0]*e[0]+x[1]*e[1]+x[2]*e[2]),-(y[0]*e[0]+y[1]*e[1]+y[2]*e[2]),-(z[0]*e[0]+z[1]*e[1]+z[2]*e[2]),1];},
 trs(tx,ty,tz,ry,rx,rz,s){ry=ry||0;rx=rx||0;rz=rz||0;s=s===undefined?1:s;const sx=Array.isArray(s)?s[0]:s,sy=Array.isArray(s)?s[1]:s,sz=Array.isArray(s)?s[2]:s;
  let m=[sx,0,0,0,0,sy,0,0,0,0,sz,0,0,0,0,1];
  if(rz){const c=Math.cos(rz),n=Math.sin(rz);m=M4.mul([c,n,0,0,-n,c,0,0,0,0,1,0,0,0,0,1],m);}
  if(rx){const c=Math.cos(rx),n=Math.sin(rx);m=M4.mul([1,0,0,0,0,c,n,0,0,-n,c,0,0,0,0,1],m);}
  if(ry){const c=Math.cos(ry),n=Math.sin(ry);m=M4.mul([c,0,-n,0,0,1,0,0,n,0,c,0,0,0,0,1],m);}
  m[12]=tx;m[13]=ty;m[14]=tz;return m;}
};
const tfp=(m,p)=>[m[0]*p[0]+m[4]*p[1]+m[8]*p[2]+m[12],m[1]*p[0]+m[5]*p[1]+m[9]*p[2]+m[13],m[2]*p[0]+m[6]*p[1]+m[10]*p[2]+m[14]];
/* ---------- Mesh-Builder ---------- */
function mkB(){return{v:[],m:M4.id()};}
function use(B,m,fn){const o=B.m;B.m=M4.mul(o,m);fn();B.m=o;}
function T3(B,a,b,c,col,e,ctr,j){
 const A=tfp(B.m,a),Bb=tfp(B.m,b),C=tfp(B.m,c);
 const ux=Bb[0]-A[0],uy=Bb[1]-A[1],uz=Bb[2]-A[2],vx=C[0]-A[0],vy=C[1]-A[1],vz=C[2]-A[2];
 let nx=uy*vz-uz*vy,ny=uz*vx-ux*vz,nz=ux*vy-uy*vx;const l=Math.hypot(nx,ny,nz);if(l<1e-9)return;nx/=l;ny/=l;nz/=l;
 if(ctr){const cc=tfp(B.m,ctr);if(nx*((A[0]+Bb[0]+C[0])/3-cc[0])+ny*((A[1]+Bb[1]+C[1])/3-cc[1])+nz*((A[2]+Bb[2]+C[2])/3-cc[2])<0){nx=-nx;ny=-ny;nz=-nz;}}
 const k=1+(rnd()-.5)*(j===undefined?.12:j),r=Math.min(1,col[0]*k),g=Math.min(1,col[1]*k),b2=Math.min(1,col[2]*k),E=e||0;
 const v=B.v;v.push(A[0],A[1],A[2],nx,ny,nz,r,g,b2,E,Bb[0],Bb[1],Bb[2],nx,ny,nz,r,g,b2,E,C[0],C[1],C[2],nx,ny,nz,r,g,b2,E);
}
const C_=c=>typeof c==='string'?hx(c):c;
function box(B,x,y,z,sx,sy,sz,col,e,j){col=C_(col);const X=sx/2,Z=sz/2,Y1=y+sy,ct=[x,y+sy/2,z];
 const P=[[x-X,y,z-Z],[x+X,y,z-Z],[x+X,y,z+Z],[x-X,y,z+Z],[x-X,Y1,z-Z],[x+X,Y1,z-Z],[x+X,Y1,z+Z],[x-X,Y1,z+Z]];
 for(const f of[[0,1,2,3],[7,6,5,4],[0,4,5,1],[1,5,6,2],[2,6,7,3],[3,7,4,0]]){T3(B,P[f[0]],P[f[1]],P[f[2]],col,e,ct,j);T3(B,P[f[0]],P[f[2]],P[f[3]],col,e,ct,j);}}
function cone(B,x,y,z,r,h,n,col,e,j,ph){col=C_(col);ph=ph||0;n=n||6;const ct=[x,y+h*.35,z],ap=[x,y+h,z];
 for(let k=0;k<n;k++){const a=ph+k/n*PI*2,b=ph+(k+1)/n*PI*2,p0=[x+Math.cos(a)*r,y,z+Math.sin(a)*r],p1=[x+Math.cos(b)*r,y,z+Math.sin(b)*r];T3(B,p0,p1,ap,col,e,ct,j);T3(B,p0,p1,[x,y,z],col,e,ct,j);}}
function cyl(B,x,y,z,r,h,n,col,e,rt,j,ph){col=C_(col);n=n||6;ph=ph||0;rt=rt===undefined?r:rt;const ct=[x,y+h/2,z];
 for(let k=0;k<n;k++){const a=ph+k/n*PI*2,b=ph+(k+1)/n*PI*2,ca=Math.cos(a),sa=Math.sin(a),cb=Math.cos(b),sb=Math.sin(b);
  const p0=[x+ca*r,y,z+sa*r],p1=[x+cb*r,y,z+sb*r],q0=[x+ca*rt,y+h,z+sa*rt],q1=[x+cb*rt,y+h,z+sb*rt];
  T3(B,p0,p1,q1,col,e,ct,j);T3(B,p0,q1,q0,col,e,ct,j);T3(B,p0,p1,[x,y,z],col,e,ct,j);if(rt>0)T3(B,q0,q1,[x,y+h,z],col,e,ct,j);}}
function sph(B,x,y,z,rx,ry,rz,col,e,la,lo,jit,j){col=C_(col);la=la||4;lo=lo||7;jit=jit||0;
 const pt=(i,k)=>{const th=i/la*PI,ph=k/lo*PI*2,f=(i===0||i===la)?1:1+(hs(i*7.1+x,(k%lo)*3.3+z)-.5)*jit;return[x+Math.sin(th)*Math.cos(ph)*rx*f,y+Math.cos(th)*ry*f,z+Math.sin(th)*Math.sin(ph)*rz*f];};
 for(let i=0;i<la;i++)for(let k=0;k<lo;k++){const a=pt(i,k),b=pt(i+1,k),c=pt(i+1,k+1),d=pt(i,k+1),ct=[x,y,z];if(i>0)T3(B,a,b,d,col,e,ct,j);if(i<la-1)T3(B,b,c,d,col,e,ct,j);}}
/* flache Polygon-Platte (Sternform um den Ursprung) in der XY-Ebene, Dicke z0..z1 */
function plate(B,pts,z0,z1,col,e,j){col=C_(col);const n=pts.length,ct=[0,0,(z0+z1)/2];
 for(let k=0;k<n;k++){const a=pts[k],b=pts[(k+1)%n];T3(B,[0,0,z1],[a[0],a[1],z1],[b[0],b[1],z1],col,e,ct,j);T3(B,[0,0,z0],[a[0],a[1],z0],[b[0],b[1],z0],col,e,ct,j);
  T3(B,[a[0],a[1],z0],[b[0],b[1],z0],[b[0],b[1],z1],col,e,ct,j);T3(B,[a[0],a[1],z0],[b[0],b[1],z1],[a[0],a[1],z1],col,e,ct,j);}}
const starPts=(r1,r2,n)=>{const p=[];for(let k=0;k<n*2;k++){const a=k/(n*2)*PI*2,r=k%2?r2:r1;p.push([Math.cos(a)*r,Math.sin(a)*r]);}return p;};
/* Dach mit Giebel: Breite w (x), Höhe h, Tiefe d (z) */
function gable(B,x,y,z,w,h,d,col,e){col=C_(col);const X=w/2,Z=d/2,ap0=[x,y+h,z-Z],ap1=[x,y+h,z+Z],ct=[x,y+h*.3,z];
 const a=[x-X,y,z-Z],b=[x+X,y,z-Z],c=[x+X,y,z+Z],dd=[x-X,y,z+Z];
 T3(B,a,b,ap0,col,e,ct);T3(B,a,dd,ap1,col,e,ct);T3(B,dd,c,ap1,col,e,ct);T3(B,b,c,ap1,col,e,ct);T3(B,a,ap0,ap1,col,e,ct);T3(B,b,ap0,ap1,col,e,ct);T3(B,a,ap1,dd,col,e,ct);T3(B,a,ap0,ap1,col,e,ct);
 T3(B,a,b,c,col,e,ct);T3(B,a,c,dd,col,e,ct);}
const fin=B=>({d:new Float32Array(B.v),n:B.v.length/10,buf:null});
/* ---------- Pfad & Gelände ---------- */
const MAXI=20,NI=i=>i<0?-19:i*15,NZ=i=>i<0?1.5:3.4*Math.sin(i*.85+.4)+1.6*Math.sin(i*2.1);
const gH=x=>x*.05+1.6*Math.sin(x/37);
const PTS={};for(let i=-2;i<=MAXI+2;i++)PTS[i]=[i<-1?NI(-1)-15:i>MAXI?NI(MAXI)+15:NI(i),i<-1?1.5:i>MAXI?NZ(MAXI):NZ(i)];
function sp(u){u=cl(u,-1,MAXI);const k=Math.min(MAXI-1,Math.floor(u)),t=u-k;const p0=PTS[k-1],p1=PTS[k],p2=PTS[k+1],p3=PTS[k+2],t2=t*t,t3=t2*t;
 const f=i=>.5*((2*p1[i])+(-p0[i]+p2[i])*t+(2*p0[i]-5*p1[i]+4*p2[i]-p3[i])*t2+(-p0[i]+3*p1[i]-3*p2[i]+p3[i])*t3);return[f(0),f(1)];}
const PX=[],PZ=[],PU=[];for(let u=-1;u<=MAXI+.0001;u+=.02){const p=sp(u);PU.push(u);PX.push(p[0]);PZ.push(p[1]);}
function pathZ(x){if(x<=PX[0])return PZ[0];if(x>=PX[PX.length-1])return PZ[PZ.length-1];let a=0,b=PX.length-1;while(b-a>1){const m=(a+b)>>1;if(PX[m]<=x)a=m;else b=m;}const t=(x-PX[a])/(PX[b]-PX[a]||1);return PZ[a]+(PZ[b]-PZ[a])*t;}
const nodeY=i=>gH(NI(i))+.1;
function hAt(x,z){const pz=pathZ(x),dz=z-pz,d=Math.abs(dz),fl=sm(3.4,15,d),nz=fbm(x*.09,z*.09);
 const amp=dz>0?fl*(1+3.2*sm(14,40,d)):fl*(2.6+7.5*sm(10,40,d));let h=gH(x)+nz*amp+fbm(x*.3,z*.3)*.12*(1-fl*.5)+(dz<0?fl*1.4:0);
 let k=cl(Math.round(x/15),0,MAXI);let best=1e9,ky=0;const cand=[k];if(x<-6)cand.push(-1);for(const c of cand){const dd=Math.hypot(x-NI(c),z-NZ(c));if(dd<best){best=dd;ky=nodeY(c);}}
 if(best<5.2)h=ky+(h-ky)*sm(2.6,5.2,best);return h;}
/* ---------- Biome ---------- */
let PAL=null;const hxp=i=>PAL[cl(i,0,20)].map(hx);
function palAt(x){const t=cl(x/15,0,MAXI),i0=Math.floor(t),i1=Math.min(MAXI,i0+1),f=t-i0,a=hxp(i0),b=hxp(i1);return a.map((c,k)=>mixc(c,b[k],f));}
function terrainColor(x,z,y,d){const p=palAt(x);let c=mixc(mixc(p[2],p[1],.28),p[0],sm(5,24,d));c=mixc(c,p[1],cl((y-gH(x))*.06,0,.35));return c;}
/* ---------- Props ---------- */
function pMush(B,x,y,z,s,col){const R=rnd;cyl(B,x,y,z,.22*s,.9*s,6,'#eadcc2',0,.2*s);cone(B,x,y+.8*s,z,.95*s,.6*s,7,col,.1);cone(B,x+1.1*s,y,z+.5*s,.12*s,.5*s,5,'#eadcc2',0);cone(B,x+1.1*s,y+.4*s,z+.5*s,.5*s,.35*s,6,col,.1);}
function pCrys(B,x,y,z,s,cols,em){const n=3+(rnd()*3|0);for(let k=0;k<n;k++){const h=(1.2+rnd()*2.2)*s,r=(.28+rnd()*.25)*s,ox=(rnd()-.5)*1.6*s,oz=(rnd()-.5)*1.6*s,col=cols[(rnd()*cols.length)|0];
 use(B,M4.trs(x+ox,y,z+oz,rnd()*6,(rnd()-.5)*.5,(rnd()-.5)*.5),()=>cone(B,0,0,0,r,h,5,col,em,.16));}}
function pPine(B,x,y,z,s,g,snow){cyl(B,x,y,z,.2*s,.9*s,5,'#4a3320',0);for(let k=0;k<3;k++)cone(B,x,y+.7*s+k*.85*s,z,(1.25-k*.3)*s,1.5*s,6,g[k%g.length],0,.14);if(snow)cone(B,x,y+2.5*s,z,.4*s,.6*s,6,'#f2f7ff',.05);}
function pRock(B,x,y,z,s,col){sph(B,x,y+.25*s,z,.9*s,.65*s,.8*s,col,0,3,6,.45,.16);}
function pCloud(B,x,y,z,s){const c='#f4f6ff';sph(B,x,y,z,1.3*s,.7*s,1*s,c,.18,3,7,.1,.05);sph(B,x+1.2*s,y-.1*s,z+.2*s,.9*s,.55*s,.8*s,c,.18,3,6,.1,.05);sph(B,x-1.1*s,y-.15*s,z-.2*s,.8*s,.5*s,.7*s,c,.18,3,6,.1,.05);}
function pStar(B,x,y,z,s,col){use(B,M4.trs(x,y,z,rnd()*3),()=>{cone(B,0,0,0,.35*s,.9*s,4,col,.9,0);cone(B,0,0,0,.35*s,-.9*s,4,col,.9,0);});}
function pFlower(B,x,y,z,s,col){cyl(B,x,y,z,.05*s,1.2*s,4,'#3a8a3a',0);sph(B,x,y+1.25*s,z,.45*s,.2*s,.45*s,col,.2,2,6,0,.05);}
const BIOME=[['mush','pine'],['crys','rock'],['pine','mush'],['pine','rock'],['pine','rock'],['crys','rock'],['pine','rock'],['crys','crys'],['rock','rock'],['rock','crys'],
 ['cloud','star'],['cloud','cloud'],['cloud','flower'],['cloud','flower'],['cloud','cloud'],['flower','cloud'],['star','cloud'],['cloud','flower'],['rock','cloud'],['rock','cloud'],['cloud','star']];
const CRYS=[['#7fd8ff','#9a7aff'],['#c9a6ff','#8f6bff'],['#7ff0c4','#7fd8ff'],['#8f6bff','#7ff0c4']];
function addProps(chunkB,i,lmPos){const r=rnd,biome=BIOME[i],cnt=i<10?20:14;
 for(let k=0;k<cnt;k++){const x=NI(i)+(r()-.5)*26,side=r()<.5?-1:1,z=pathZ(x)+side*(4.2+r()*(side<0?24:12));
  let ok=true;for(let n=Math.max(0,i-1);n<=Math.min(MAXI,i+1);n++)if(Math.hypot(x-NI(n),z-NZ(n))<5.3)ok=false;
  if(i>=0&&Math.hypot(x-lmPos[0],z-lmPos[2])<7)ok=false;if(!ok)continue;
  const y=hAt(x,z),B=chunkB(x),front=z>pathZ(x),s=(.8+r()*1.1)*(front?.55:1),kind=front?(biome.includes('cloud')?'cloud':['mush','rock','flower'][(r()*3)|0]):biome[(r()*biome.length)|0],p=hxp(i);
  if(kind==='mush')pMush(B,x,y,z,s*1.2,['#ffa83a','#e0558f','#ff7a4a','#ffd166','#c98bff'][(r()*5)|0]);
  else if(kind==='crys')pCrys(B,x,y,z,s,CRYS[i%4],.25);
  else if(kind==='pine')pPine(B,x,y,z,s*1.3,[mixc(p[2],hx('#1f6040'),.5),mixc(p[2],hx('#2f8a58'),.4)],i===4||i===5||i===8);
  else if(kind==='rock')pRock(B,x,y,z,s*1.2,mixc(p[3],p[1],.35));
  else if(kind==='cloud')pCloud(B,x,y+1.5+r()*3,z,s*1.1);
  else if(kind==='star')pStar(B,x,y+1.5+r()*3,z,s*1.4,['#fff2a8','#ffe27a','#c9d6ff'][(r()*3)|0]);
  else pFlower(B,x,y,z,s*1.3,['#ffd24a','#ff8fb0','#fff2a8'][(r()*3)|0]);}}
/* ---------- Wahrzeichen (lokal um (0,0,0), Basis y=0, Blick von +z) ---------- */
const WH='#f4f6ff';
function LM(i){const B=mkB(),parts=[];const P=(fn,mat,em)=>{const b=mkB();fn(b);parts.push({m:fin(b),f:mat,em:em||0});};
 const fl=(t,a,s)=>.5+.5*Math.sin(t*s+a);
 switch(i){
 case 0:{use(B,M4.trs(0,0,0,.78),()=>{cone(B,0,0,0,2.4,3.4,4,'#d8553a',0,.1);cone(B,0,0,0,2.43,2.1,4,'#f0e2c4',0,.05);});box(B,1.7,0,1.55,.9,1.7,.2,'#2a1810',0);
  cyl(B,-3.6,0,.5,.08,4.6,5,'#6b4a2f',0);box(B,-3.0,3.6,.5,1.3,.8,.1,'#ff5a4a',.15);
  for(let k=0;k<6;k++){const a=k/6*PI*2;sph(B,3.4+Math.cos(a)*.8,.25,2.4+Math.sin(a)*.8,.32,.25,.3,'#6a6a78',0,2,5,.3);}
  pPine(B,-5.5,0,-2.5,2.2,['#1f6040','#2f8a58']);pPine(B,5.5,0,-3,1.8,['#1f6040','#2f8a58']);
  P(b=>{cone(b,0,0,0,.55,1.3,5,'#ff9a2a',.8,0);cone(b,0,0,0,.28,.8,5,'#ffe27a',1,0);},t=>M4.trs(3.4,.3,2.4,t*1.5,0,0,[1,.85+.3*fl(t,0,9),1]),.2);break;}
 case 1:{const S=[[0,0,6.5,1.7,'#6d4a80'],[2.6,1,9,2,'#8a62a0'],[-2.7,.8,5.5,1.5,'#4a3560'],[1,-2.4,7.5,1.6,'#6d4a80'],[-1.2,-2,4.5,1.3,'#8a62a0']];
  S.forEach(([x,z,h,r,c],k)=>use(B,M4.trs(x,0,z,k,(k%2?.08:-.08),(k%2?-.1:.1)),()=>cone(B,0,0,0,r,h,5,c,0,.18)));
  [[-1.5,5,2.6],[3.6,6.2,-1],[0,7.4,1]].forEach(([x,y,z],k)=>P(b=>cone(b,0,0,0,.45,1.1,4,'#d8b8ff',.7,.1),t=>M4.trs(x,y+Math.sin(t*1.4+k*2)*.5,z,t*.8,0,0),.3));break;}
 case 2:{[[0,0,-.5,1.2],[-4.2,0,-2,.9],[4,0,-2.4,.95]].forEach(([x,y,z,s])=>{cyl(B,x,0,z,.5*s,3.2*s,6,'#5a3c24',0,.4*s);
  sph(B,x,3.6*s,z,2.1*s,1.5*s,2.1*s,'#2f7a52',0,3,7,.2);sph(B,x-.9*s,4.4*s,z+.3*s,1.5*s,1.2*s,1.5*s,'#3f9a5b',0,3,7,.2);sph(B,x+.9*s,4.9*s,z-.2*s,1.4*s,1.1*s,1.4*s,'#5fd08a',.05,3,7,.2);
  for(let k=0;k<5;k++){use(B,M4.trs(x+(k-2)*.7*s,5.6*s,z,0,0,(k-2)*.28),()=>cone(B,0,0,0,.16*s,2.2*s,3,WH,.25,.05));}});break;}
 case 3:{box(B,0,0,0,6.4,3,4.2,'#8a5a34',0,.08);for(let k=0;k<4;k++)box(B,0,.35+k*.7,2.12,6.45,.07,.05,'#6b4423',0);gable(B,0,3,0,7.2,2.2,4.8,'#4a2f1a',0);box(B,-1.4,0,2.12,1.1,2,.1,'#3a2410',0);box(B,1.4,1,2.12,1,.9,.1,'#ffd166',.9);
  box(B,2.4,3.4,-1.1,.8,2.4,.8,'#5a3a1a',0);for(let k=0;k<7;k++)use(B,M4.trs(-4.4+(k%4)*.0,.0,0),()=>{});
  for(let k=0;k<6;k++){const r=k<3?k:k-3,yy=k<3?.45:1.2;use(B,M4.trs(-5.6+(r-1)*.0,yy,2.4+(k<3?r*.0:.0),0,0,PI/2),()=>cyl(B,0,-1.6+r*1.05,0,.42,1.6,7,'#a8743f',0,.42));}
  cyl(B,4.2,0,1.8,.14,2.6,5,'#6b4a2f',0);
  P(b=>{plate(b,starPts(2.1,1.75,12),0,.18,'#d8dde6',.15,.06);plate(b,starPts(.55,.55,6),.18,.3,'#8a8f9c',0);},t=>M4.trs(4.2,2.5,2.0,0,0,-t*3.2),.1);break;}
 case 4:{cone(B,0,0,0,5.5,12,7,'#5a6b8f',0,.12);cone(B,0,7.6,0,2.4,4.4,7,'#f2f7ff',.08,.06);cone(B,-5.2,0,1,3,6.2,6,'#4a5a7f',0,.12);cone(B,5,0,.4,2.6,5.2,6,'#4a5a7f',0,.12);cone(B,-5.2,3.9,1,1.2,2.3,6,'#f2f7ff',.05,.05);
  for(let k=0;k<5;k++)P(b=>{sph(b,0,0,0,1.6,.8,1.2,'#2a3050',0,3,7,.2);sph(b,1.2,.2,.3,1,.6,.9,'#33395c',0,3,6,.2);},t=>M4.trs(-5+k*2.5+Math.sin(t*.3+k)*1.4,13.2+(k%2)*.8,-1,0,0,0),0);
  P(b=>{plate(b,[[0,2],[-.9,.2],[-.1,.3],[-.7,-1.8],[.9,.5],[.1,.5],[.8,2]],0,.15,'#ffe66b',1,0);},t=>(Math.sin(t*3.1)>.55||Math.sin(t*7.3)>.93)?M4.trs(1.5,10.5,3.4,0,0,0,1):M4.trs(0,-50,0),.0);break;}
 case 5:{sph(B,0,0,0,4.8,4.1,4.4,'#bfe9f7',.12,4,9,.12,.08);sph(B,0,0,0,4.9,4.2,4.5,'#9fd8ee',.0,2,9,0,.0);box(B,0,0,3.6,2.1,2.5,.9,'#0b1b2b',0);cone(B,0,0,3.6,1.05,.01,6,'#0b1b2b',0);
  for(let k=0;k<7;k++){const a=-1.1+k*.37;cone(B,Math.sin(a)*1.9,2.5-Math.abs(a)*.4,3.9+Math.cos(a)*.0,.17,-1.4-(k%3)*.3,5,'#e8fbff',.35,.08);}
  [[-5.5,2],[5.4,1.2],[0,-4.5]].forEach(([x,z],k)=>use(B,M4.trs(x,0,z,k,.1,-.1),()=>cone(B,0,0,0,.9,3.6-k*.4,5,'#cfeeff',.3,.14)));break;}
 case 6:{cyl(B,-5.8,0,0,.45,5.4,6,'#5a3a22',0);cyl(B,5.8,0,0,.45,5.4,6,'#5a3a22',0);box(B,-6.6,0,0,2.4,2.2,2.6,'#6a5a78',0,.12);box(B,6.6,0,0,2.4,2.2,2.6,'#6a5a78',0,.12);
  for(let k=0;k<=12;k++){const t=k/12,x=-5.4+t*10.8,y=4.9-Math.sin(t*PI)*1.9;box(B,x,y-.1,0,.75,.14,2,'#c9a06a',0,.1);if(k%2===0){box(B,x,y,-1.0,.08,1.1,.08,'#7a5a38',0);box(B,x,y,1.0,.08,1.1,.08,'#7a5a38',0);}}
  P(b=>{for(let k=0;k<12;k++){const t=(k+.5)/12;box(b,-5.4+t*10.8,5.9-Math.sin(t*PI)*1.9,-1.0,.9,.07,.07,'#7a5a38',0);box(b,-5.4+t*10.8,5.9-Math.sin(t*PI)*1.9,1.0,.9,.07,.07,'#7a5a38',0);}},t=>M4.trs(0,0,0,0,0,0),0);break;}
 case 7:{sph(B,0,-.4,0,4.2,2.2,3.6,'#3a2f5c',0,3,8,.3,.12);
  [['#8f6bff',-1.8,0,5.2,.9,-.15],['#7ff0c4',.4,.5,7.4,1.1,.05],['#c9a6ff',2.3,-.3,4.4,.8,.2],['#8f6bff',-.6,-1.8,3.4,.7,-.3],['#7ff0c4',1.3,1.8,3,.6,.2]].forEach(([c,x,z,h,r,l],k)=>P(b=>cone(b,0,0,0,r,h,6,c,.7,.1),t=>M4.trs(x,1.3,z,k,l,-l*.6,[1,1+.04*Math.sin(t*2+k),1]),.15+.2*fl(0,0,0)));
  P(b=>sph(b,0,0,0,5.4,2.6,4.6,'#8f6bff',.5,3,9,0,0),t=>M4.trs(0,.4,0,0,0,0,1+.04*Math.sin(t*2)),.0);parts.pop();break;}
 case 8:{[[0,0,8,1.8,'#2a2a33'],[2.6,.8,6,1.5,'#3a3c4c'],[-2.6,.6,5,1.4,'#4a4e63'],[1.2,-2.4,6.6,1.5,'#2a2a33']].forEach(([x,z,h,r,c],k)=>use(B,M4.trs(x,0,z,k*2,.07,-.06),()=>cone(B,0,0,0,r,h,5,c,0,.2)));
  for(let k=0;k<4;k++)P(b=>{sph(b,0,0,0,1.8,.9,1.4,'#23232e',0,3,7,.2);sph(b,1.4,.2,.2,1.2,.7,1,'#2c2c3a',0,3,6,.2);},t=>M4.trs(-4+k*2.7+Math.sin(t*.4+k)*1.2,10.2+(k%2)*.7,-1,0,0,0),0);
  P(b=>{plate(b,[[0,2.6],[-1.1,.3],[-.1,.4],[-.9,-2.2],[1.1,.6],[.1,.6],[1,2.6]],0,.15,'#ffe66b',1,0);},t=>(Math.sin(t*2.6)>.5||Math.sin(t*6.1)>.92)?M4.trs(.8,8.2,3,0,0,0,1):M4.trs(0,-50,0),0);break;}
 case 9:{cyl(B,0,0,0,2,6.4,8,'#8a7f9a',0,1.45,.1);for(let k=0;k<3;k++)cyl(B,0,1.3+k*1.7,0,2-k*.2,.18,8,'#5a4f6a',0,2-k*.2+.05);cyl(B,0,6.4,0,1.7,.5,8,'#4a4058',0,2.1);box(B,0,0,1.8,.9,1.5,.2,'#2a1f35',0);box(B,0,3,1.45,.7,.9,.2,'#ffd166',.9);
  for(let k=0;k<4;k++)box(B,-1.6+k*1.1,0,2.4+(k%2)*.2,1,.5+k*.15,.6,'#6a5f7a',0);
  P(b=>{cone(b,0,0,0,.9,2,6,'#ff9a2a',.9,0);cone(b,0,0,0,.5,1.4,6,'#ffe27a',1,0);},t=>M4.trs(0,6.9,0,t*2,0,0,[1,.85+.25*fl(t,0,11),1]),.3);
  P(b=>sph(b,0,0,0,2.7,2.7,2.7,'#ffce67',.5,2,7,0,0),t=>M4.trs(0,7.6,0,0,0,0,.9+.12*fl(t,0,5)),.0);parts.pop();break;}
 case 10:{[-3.2,3.2].forEach(x=>{cyl(B,x,0,0,.8,6.4,8,WH,.06,.7,.05);box(B,x,6.4,0,2.0,.5,2.0,'#e6ebff',.05);box(B,x,-.3,0,2.4,.5,2.4,'#dfe4f8',.05);});box(B,0,6.6,0,8.4,.9,1.8,WH,.06);cone(B,0,7.5,0,1.1,1.1,4,'#ffe27a',.9,0);
  P(b=>box(b,0,0,0,5.6,6.2,.2,'#ffe6a8',1,0),t=>M4.trs(0,0,0,0,0,0,[1,1,1]),.2+.15*Math.sin(0));parts.pop();box(B,0,.2,0,5.6,6.2,.2,'#ffc860',.8,0);
  [[-5.6,0,1.5,1],[5.5,0,1,.9],[0,0,3,1.1]].forEach(([x,y,z,s])=>pCloud(B,x,y+.5,z,s*1.2));break;}
 case 11:{[[-4.5,1.5,0,1.1],[0,3.4,-1,1.3],[4.6,5,0,1],[8.4,6.8,-1.4,1.2]].forEach(([x,y,z,s],k)=>P(b=>pCloud(b,0,0,0,s*1.6),t=>M4.trs(x-4+Math.sin(t*.5+k)*.5,y+Math.sin(t*.9+k*1.7)*.35,z),.1));break;}
 case 12:{[[-3.6,4.2,1,'#ff6a8a'],[0,5.3,1.8,'#ffd166'],[3.8,4.4,-1.2,'#6ad8ff']].forEach(([x,h,sp,c],k)=>{cyl(B,x,0,0,.12,h,5,'#d8c8a8',0);sph(B,x,h,.1,.22,.22,.22,'#ffffff',.2,2,5);
  P(b=>{for(let q=0;q<4;q++){use(b,M4.trs(0,0,0,0,0,q*PI/2),()=>{plate(b,[[0,0],[1.7,.1],[1.7,1.5]],0,.07,c,.15,.05);});}},t=>M4.trs(x,h,.35,0,0,-t*(sp+k*.4)),.12);});break;}
 case 13:{const cs=['#ff4a4a','#ff9a3a','#ffe14a','#4fe07a','#4a9aff','#a06aff'];cs.forEach((c,k)=>{const R=7.4-k*.5;for(let q=0;q<14;q++){const a0=q/14*PI,a1=(q+1)/14*PI,x0=Math.cos(a0)*R,y0=Math.sin(a0)*R*.8,x1=Math.cos(a1)*R,y1=Math.sin(a1)*R*.8;const mx=(x0+x1)/2,my=(y0+y1)/2,len=Math.hypot(x1-x0,y1-y0)+.12;
   use(B,M4.trs(mx,my,0,0,0,Math.atan2(y1-y0,x1-x0)),()=>box(B,0,-.25,0,len,.5,.9,c,.55,.04));}});
  [[-7.6,.7],[7.6,.7]].forEach(([x,y],k)=>{pCloud(B,x,y,0,1.5);pCloud(B,x+(k?-1.2:1.2),y-.2,1,1.1);});break;}
 case 14:{for(let k=0;k<6;k++)P(b=>{sph(b,0,0,0,2.1,1.1,1.6,'#4a4e63',0,3,7,.2);sph(b,1.6,.3,.3,1.5,.8,1.2,'#565a72',0,3,7,.2);},t=>M4.trs(-5+k*2+Math.sin(t*.35+k)*.9,8.4+(k%2)*.8,-1.2+(k%3)*.8),0);
  P(b=>{for(let q=0;q<10;q++)box(b,(q-4.5)*1.1,0,(q%3-1)*1.1,.07,.9,.07,'#9fd0ff',.5,0);},t=>M4.trs(0,7.6-((t*6)%4.2),0),0);
  P(b=>{plate(b,[[0,2.6],[-1.1,.3],[-.1,.4],[-.9,-2.2],[1.1,.6],[.1,.6],[1,2.6]],0,.15,'#fff27a',1,0);},t=>(Math.sin(t*2.2)>.45||Math.sin(t*5.7)>.9)?M4.trs(1.2,5.8,2.2,0,0,0,1):M4.trs(0,-50,0),0);break;}
 case 15:{[-4,-1.7,.6,2.9,4.9].forEach((x,k)=>{const hh=2.2+(k%2)*.6;cyl(B,x,0,2.4-(k%2)*1.2,.1,hh,4,'#3a8a3a',0);sph(B,x,hh+.2,2.5-(k%2)*1.2,.75,.75,.25,'#ffd24a',.3,2,8,0,.05);sph(B,x,hh+.2,2.6-(k%2)*1.2,.32,.32,.2,'#6b3f1a',0,2,6);});
  P(b=>{plate(b,starPts(3.4,2.5,14),0,.3,'#ffc03a',.9,.05);plate(b,[[2.2,0],[1.5,1.6],[0,2.2],[-1.5,1.6],[-2.2,0],[-1.5,-1.6],[0,-2.2],[1.5,-1.6]],.3,.5,'#fff2a8',1,0);},t=>M4.trs(0,6.8,-1.6,0,0,t*.4),.2);break;}
 case 16:{[[-3,4.2,1],[0,6.4,-.5],[3.2,3.6,0],[-1,2.4,2.4],[2,5.6,2]].forEach(([x,y,z],k)=>P(b=>{cone(b,0,0,0,.6,1.5,4,k%2?'#fff2a8':'#c9d6ff',.9,0);cone(b,0,0,0,.6,-1.5,4,k%2?'#ffe27a':'#aeb9ff',.9,0);},t=>M4.trs(x,y+Math.sin(t*1.1+k*1.6)*.45,z,t*.9+k),.3));
  cyl(B,0,0,0,3.8,.25,12,'#161650',.2,3.8);cyl(B,0,.25,0,3.2,.06,12,'#3a4aa8',.6,3.2);break;}
 case 17:{cyl(B,0,0,0,2.3,5.6,8,'#e8d8c0',0,1.5,.08);cone(B,0,5.6,0,1.9,1.8,8,'#c04a3a',0,.1);box(B,0,0,2.1,1,1.6,.2,'#4a2f1a',0);box(B,0,3,1.7,.7,.7,.2,'#ffd166',.9);cyl(B,0,4.6,1.5,.3,.7,6,'#4a2f1a',0,.3);
  P(b=>{for(let q=0;q<4;q++)use(b,M4.trs(0,0,0,0,0,q*PI/2),()=>{box(b,-.2,.4,0,.4,4,.12,'#8a5a34',0);box(b,.2,1.3,0,1.3,2.8,.08,'#f2ead8',0);});},t=>M4.trs(0,4.8,2.0,0,0,-t*.7),0);break;}
 case 18:{[[-3.6,0,-.5,1.1],[0,0,-2,1.3],[3.8,0,-.8,1]].forEach(([x,y,z,s],k)=>{cyl(B,x,0,z,.38*s,4.6*s,6,'#4a4a56',0,.14*s,.1);[[0,3.3],[-1,2.6],[1.1,3.9]].forEach(([dx,dy],q)=>sph(B,x+dx*s,dy*s+.5,z+(q-1)*.4,1.1*s,.7*s,.9*s,'#6a6a7c',.05,3,6,.2,.08));});
  for(let k=0;k<4;k++)P(b=>{sph(b,0,0,0,4.2,.45,3.2,'#d8e0ec',.25,2,9,0,.05);},t=>M4.trs(Math.sin(t*.4+k*1.7)*1.4,.6+k*.55,Math.cos(t*.3+k)*1.2),0);
  P(b=>{sph(b,0,0,0,.45,.6,.45,'#f4fbff',.9,2,6,0,0);},t=>M4.trs(-2+Math.sin(t*.8)*3.4,2.6+Math.sin(t*1.7)*.5,2.6),.2);break;}
 case 19:{cyl(B,0,0,0,2.4,9,8,'#4a4a62',0,1.6,.1);for(let k=0;k<4;k++)cyl(B,0,1.4+k*2,0,2.4-k*.18,.22,8,'#33334a',0,2.4-k*.18+.05);cone(B,0,9,0,2,3.2,8,'#2a2a3e',0,.1);cyl(B,0,12.1,0,.07,1.8,4,'#c8c8d8',0);box(B,0,0,2.2,1.1,1.8,.2,'#1c1c2e',0);box(B,0,5,1.5,.8,1,.2,'#ffe66b',.8);
  for(let k=0;k<3;k++)P(b=>{sph(b,0,0,0,2.2,1,1.6,'#33334a',0,3,7,.2);},t=>M4.trs(-5+k*5+Math.sin(t*.4+k)*.8,10.4-(k%2)*.9,-1.8),0);
  P(b=>{plate(b,[[0,3.4],[-1.3,.4],[-.1,.5],[-1.1,-2.8],[1.3,.8],[.1,.8],[1.2,3.4]],0,.18,'#fff27a',1,0);},t=>(Math.sin(t*2.4)>.5||Math.sin(t*6.7)>.9)?M4.trs(2.3,7,2.3,0,0,0,1):M4.trs(0,-50,0),0);break;}
 default:{[-4,4].forEach(x=>{cyl(B,x,0,0,.95,7,8,'#ffe3a8',.1,.8,.05);box(B,x,7,0,2.4,.55,2.4,'#fff0c8',.15);box(B,x,-.3,0,2.8,.5,2.8,'#f0d898',.1);cone(B,x,7.55,0,.7,1.1,4,'#ffc03a',.6,0);});
  box(B,0,7.2,0,10,.9,2,'#fff0c8',.15);cone(B,0,8.1,0,5,2.1,4,'#ffe3a8',.15,.05,PI/4);box(B,-2.6,0.2,0,5.2,6.9,.2,'#fff7d8',1);
  for(let k=0;k<5;k++)box(B,0,k*.22,2.3+(4-k)*.8,6-k*.4,.22,.9,'#f6e6b8',.1);
  P(b=>{plate(b,starPts(1.5,1,12),0,.3,'#fff2a8',1,0);},t=>M4.trs(0,10.5,0,0,0,t*.5),.2);}}
 return{b:fin(B),parts};}
/* ---------- Hütte ---------- */
function buildHut(){const B=mkB();box(B,0,0,0,5,2.8,3.8,'#8b5a2b',0,.08);for(let k=0;k<4;k++)box(B,0,.3+k*.65,1.92,5.05,.07,.05,'#6b4423',0);gable(B,0,2.8,0,5.8,2.2,4.4,'#4a2f1a',0);box(B,0,0,1.92,1,2,.1,'#3a2410',0);box(B,-1.7,1,1.92,.9,.8,.1,'#ffd166',.9);box(B,1.5,3.2,-.8,.7,2,.7,'#5a3a1a',0);
 const sm=mkB();[0,1,2,3].forEach(k=>sph(sm,0,k*1.3,0,.4+k*.12,.4+k*.12,.4+k*.12,'#f0f0f8',.2,2,5,0,.05));
 return{b:fin(B),smoke:fin(sm)};}
/* ---------- Avatar (Beere) ---------- */
function buildAvatar(){const B=mkB();sph(B,0,.75,0,.7,.82,.7,'#ff5d6c',.1,4,8,0,.08);sph(B,-.25,1.25,.5,.18,.14,.1,'#ffffff',.8,2,5,0,0);box(B,-.28,.78,.62,.15,.2,.12,'#2a1520',0);box(B,.14,.78,.62,.15,.2,.12,'#2a1520',0);box(B,-.35,0,.15,.26,.2,.3,'#e04a5a',0);box(B,.12,0,.15,.26,.2,.3,'#e04a5a',0);
 cone(B,0,1.5,0,.34,.35,5,'#4fc06a',.1,.1);cyl(B,0,1.78,0,.05,.32,4,'#2f8a48',0);return fin(B);}
function buildStones(){const out={};for(let s=-1;s<MAXI;s++){const B=mkB();let acc=0,pu=s,pp=sp(s);for(let u=s+.01;u<=s+1;u+=.01){const p=sp(u),dx=p[0]-pp[0],dz=p[1]-pp[1];acc+=Math.hypot(dx,dz);
  const dA=Math.hypot(p[0]-NI(s),p[1]-NZ(s)),dB=Math.hypot(p[0]-NI(s+1),p[1]-NZ(s+1));
  if(acc>1.4&&dA>3.1&&dB>3.1){acc=0;const y=hAt(p[0],p[1])+.02,ang=Math.atan2(dx,dz);const tgt=Math.atan2(dz,dx);
   use(B,M4.trs(p[0],y,p[1],-tgt,0,0,[.95+rnd()*.25,1,.62+rnd()*.15]),()=>cyl(B,0,0,0,.68,.2,7,'#e8c78a',.12,.62,.08));}pp=p;}
  out[s]=fin(B);}return out;}
function buildNode(){const B=mkB();cyl(B,0,0,0,2.65,.5,14,'#2a1b3d',0,2.5,.05);const T=mkB();cyl(T,0,.5,0,2.05,.16,14,[1,1,1],0,1.95,.05);const R=mkB();for(let k=0;k<24;k++){const a=k/24*PI*2,b=(k+1)/24*PI*2,ca=Math.cos(a),sa=Math.sin(a),cb=Math.cos(b),sb=Math.sin(b),r0=2.72,r1=2.98;const c='#ffe9a0';T3(R,[ca*r0,0,sa*r0],[ca*r1,0,sa*r1],[cb*r1,0,sb*r1],hx(c),1,[0,-1,0],0);T3(R,[ca*r0,0,sa*r0],[cb*r1,0,sb*r1],[cb*r0,0,sb*r0],hx(c),1,[0,-1,0],0);}
 return{ring:fin(B),top:fin(T),sel:fin(R)};}
/* ---------- Szene ---------- */
const S={dir:1,av:{x:0,y:0,k:26},sky:[[.1,.1,.2],[.4,.5,.7]],ok:false,W:960,H:540,u:0,face:0,cx:0,cy:0,cz:0,moving:false,sxs:[],sys:[],bxs:[],bys:[],hut:{x:0,y:0},proj:null};
const SKYC=[];let chunks=[],LMs=[],stones,node,hut,avatar,shadow,fly,VP=null,EYE=[0,0,0];
const CHW=32,CH0=-60;
function buildWorld(opts){PAL=opts.PAL;(opts.SKY||[]).forEach((a,i)=>{SKYC[i]=a.map(hx);});seed=777;
 const nch=Math.ceil((NI(MAXI)+60-CH0)/CHW),CB=[];for(let k=0;k<nch;k++)CB.push(mkB());const cb=x=>CB[cl(Math.floor((x-CH0)/CHW),0,nch-1)];
 const x0=-55,x1=NI(MAXI)+55,z0=-58,z1=44,st=2.5;
 for(let x=x0;x<x1;x+=st)for(let z=z0;z<z1;z+=st){const h00=hAt(x,z),h10=hAt(x+st,z),h01=hAt(x,z+st),h11=hAt(x+st,z+st);const cxm=x+st/2,czm=z+st/2,d=Math.abs(czm-pathZ(cxm)),B=cb(cxm);
  const flip=hs(x*.31,z*.17)>.5;const tris=flip?[[[x,h00,z],[x,h01,z+st],[x+st,h11,z+st]],[[x,h00,z],[x+st,h11,z+st],[x+st,h10,z]]]:[[[x,h00,z],[x,h01,z+st],[x+st,h10,z]],[[x+st,h10,z],[x,h01,z+st],[x+st,h11,z+st]]];
  for(const t of tris){const cy=(t[0][1]+t[1][1]+t[2][1])/3,cx2=(t[0][0]+t[1][0]+t[2][0])/3;const col=terrainColor(cx2,czm,cy,d);const a=t[0],b=t[1],c=t[2];
   const ux=b[0]-a[0],uy=b[1]-a[1],uz=b[2]-a[2],vx=c[0]-a[0],vy=c[1]-a[1],vz=c[2]-a[2];let ny=uz*vx-ux*vz;const sg=ny<0?-1:1;
   T3(B,t[0],sg>0?t[1]:t[2],sg>0?t[2]:t[1],col,0,null,.16);}}
 LMs=[];const lmPos=[];
 for(let i=0;i<=MAXI;i++){const lx=NI(i)-5.8,lz=NZ(i)-7.2,ly=hAt(lx,lz);lmPos.push([lx,ly,lz]);}
 for(let i=0;i<=MAXI;i++){addProps(cb,i,lmPos[i]);const l=LM(i);l.pos=lmPos[i];LMs.push(l);}
 chunks=CB.map((B,k)=>({m:fin(B),cx:CH0+(k+.5)*CHW}));
 stones=buildStones();node=buildNode();hut=buildHut();avatar=buildAvatar();{const SB=mkB();cyl(SB,0,0,0,.95,.05,10,[1,1,1],0,.95,0);shadow=fin(SB);}
 const FB=mkB();cone(FB,0,0,0,.12,.22,4,[1,1,1],1,0);cone(FB,0,0,0,.12,-.22,4,[1,1,1],1,0);fly=fin(FB);
 S.ok=true;}
const I4=M4.id(),WHT=[1,1,1];
function placeLM(i){const l=LMs[i];return M4.trs(l.pos[0],l.pos[1],l.pos[2],-.12,0,0,1.1);}
function camUpdate(st,dt,snap){const tu=st.sel;
 if(snap){S.u=tu;}else{const d=tu-S.u;S.moving=Math.abs(d)>.03;if(Math.abs(d)>.03)S.dir=d>0?1:-1;S.u+=d*Math.min(1,dt*6);if(!S.moving)S.u=tu;}
 const p=sp(S.u),y=hAt(p[0],p[1])+.5,k=snap?1:Math.min(1,dt*5);
 if(snap){S.cx=p[0];S.cy=y;S.cz=p[1];}else{S.cx+=(p[0]-S.cx)*k;S.cy+=(y-S.cy)*k;S.cz+=(p[1]-S.cz)*k;}
 S.ax=p[0];S.ay=y;S.az=p[1];
 const look=[S.cx+5.8,S.cy+3.2,S.cz-1.6];EYE=[look[0],look[1]+8.5,look[2]+22];
 const P=M4.persp(46*PI/180,S.W/S.H,1,320),V=M4.look(EYE,look);VP=M4.mul(P,V);
 const q=sp(S.u+.02),q2=sp(S.u-.02);let ang=0;if(S.moving){ang=Math.atan2(q[0]-q2[0],q[1]-q2[1]);S.face+=((ang-S.face+PI*3)%(PI*2)-PI)*Math.min(1,dt*10);}else S.face*=1-Math.min(1,dt*8);}
function proj(x,y,z){const m=VP,cx=m[0]*x+m[4]*y+m[8]*z+m[12],cy=m[1]*x+m[5]*y+m[9]*z+m[13],cw=m[3]*x+m[7]*y+m[11]*z+m[15];return[(cx/cw*.5+.5)*S.W,(.5-cy/cw*.5)*S.H,cw];}
function skyAt(x){if(!SKYC.length)return[[.1,.1,.2],[.4,.5,.7]];const t=cl(x/15,0,MAXI),i0=Math.floor(t),i1=Math.min(MAXI,i0+1),f=t-i0,a=SKYC[i0],b=SKYC[i1];return[mixc(a[0],b[0],f),mixc(a[1],b[1],f)];}
function collect(st,T){const L=[],mv=st.mv,u=S.u,c0=Math.floor(u)-3,c1=Math.ceil(u)+3;
 const sk=skyAt(S.cx);S.sky=sk;const fog=mixc(sk[1],palAt(S.cx)[0],.22);S.fog=fog;
 chunks.forEach(c=>{if(Math.abs(c.cx-S.cx)<CHW*3.2)L.push({m:c.m,M:I4,mul:WHT,em:0});});
 for(let s=Math.max(-1,c0);s<=Math.min(MAXI-1,c1);s++){if(s>=mv)break;const open=s+1<st.un;L.push({m:stones[s],M:I4,mul:open?[1,1,1]:[.32,.36,.5],em:open?.18:0});}
 const sxs=[],sys=[],bxs=[],bys=[];
 for(let i=Math.max(0,c0);i<=Math.min(mv,c1);i++){const y=nodeY(i),x=NI(i),z=NZ(i),locked=i>=st.un,done=!!(st.c&&st.c[i]),hid=i===10&&!st.w2;
  L.push({m:node.ring,M:M4.trs(x,y,z),mul:WHT,em:0});
  const tint=hid?[.62,.42,.95]:locked?[.38,.42,.52]:done?[.5,1,.6]:[.62,.88,.36];L.push({m:node.top,M:M4.trs(x,y,z),mul:tint,em:locked?0:.18});
  if(i===st.sel)L.push({m:node.sel,M:M4.trs(x,y+.55,z,0,0,0,1+.05*Math.sin(T*5)),mul:[1,.9,.5],em:.5+.3*Math.sin(T*5)});
  const lm=LMs[i],dim=locked?[.45,.5,.62]:WHT,PM=placeLM(i);L.push({m:lm.b,M:PM,mul:dim,em:0});
  for(const p of lm.parts)L.push({m:p.m,M:M4.mul(PM,p.f(T)),mul:dim,em:p.em});
 }
 for(let i=0;i<=MAXI;i++){const p=proj(NI(i),nodeY(i)+.6,NZ(i)),b=proj(NI(i),nodeY(i)+3.4,NZ(i));sxs[i]=p[0];sys[i]=p[1];bxs[i]=b[0];bys[i]=b[1];}
 S.sxs=sxs;S.sys=sys;S.bxs=bxs;S.bys=bys;
 if(st.hutOn){const hx0=NI(-1),hz0=NZ(-1),hy=nodeY(-1);const hzz=hz0-4.4,hm=M4.trs(hx0,hy,hzz,.1);L.push({m:node.ring,M:M4.trs(hx0,hy,hz0+.0,0,0,0,[1.2,1,1.3]),mul:WHT,em:0});
  L.push({m:hut.b,M:M4.mul(hm,M4.trs(0,.5,0)),mul:WHT,em:0});
  for(let k=0;k<4;k++){const ph=(T*.35+k*.25)%1;L.push({m:hut.smoke,M:M4.trs(hx0+1.6+ph*1.2,hy+4.9+ph*4,hzz-.8,0,0,0,.18+ph*.5),mul:[1,1,1],em:.05*(1-ph)});}
  const p=proj(hx0,hy+.5,hzz),t2=proj(hx0,hy+5.7,hzz);S.hut={x:p[0],y:p[1],top:t2[1]};}
 L.push({m:shadow,M:M4.trs(S.ax,S.ay+.02,S.az),mul:[.12,.12,.16],em:0});
 {const p=proj(S.ax,S.ay,S.az);S.av={x:p[0],y:p[1],k:(S.H/2)/(Math.tan(23*PI/180)*p[2])};}
 for(let k=0;k<26;k++){const a=k*2.399,fx=S.cx+(hs(k,1)-.3)*40+Math.sin(T*.4+k)*2,fy=S.cy+1+hs(k,2)*7+Math.sin(T*.7+k*1.3)*.6,fz=S.cz+(hs(k,3)-.7)*26;L.push({m:fly,M:M4.trs(fx,fy,fz,T+k,0,0,1),mul:k%3?[1,.7,.35]:[.5,.7,1],em:0});}
 return L;}
/* ---------- WebGL ---------- */
let gl=null,cv=null,LOC=null;
function glInit(){try{cv=document.createElement('canvas');cv.width=S.W/2|0;cv.height=S.H/2|0;gl=cv.getContext('webgl',{antialias:false,alpha:true,depth:true,preserveDrawingBuffer:true});}catch(e){gl=null;}
 if(!gl)return false;
 const vs='attribute vec3 aP;attribute vec3 aN;attribute vec3 aC;attribute float aE;uniform mat4 uVP;uniform mat4 uM;uniform mat3 uR;varying vec3 vN;varying vec3 vC;varying float vE;varying float vD;void main(){vec4 w=uM*vec4(aP,1.);vN=uR*aN;vC=aC;vE=aE;gl_Position=uVP*w;vD=gl_Position.w;}';
 const fs='precision mediump float;varying vec3 vN;varying vec3 vC;varying float vE;varying float vD;uniform vec3 uMul;uniform vec3 uFog;uniform float uEm;void main(){vec3 n=normalize(vN);vec3 L=normalize(vec3(-.35,.8,.5));float d=max(dot(n,L),0.);vec3 c=vC*uMul;vec3 lit=c*(vec3(.66,.68,.78)+vec3(.62,.54,.42)*d)+c*(vE+uEm);float f=clamp((vD-38.)/85.,0.,1.);lit=mix(lit,uFog,f);gl_FragColor=vec4(lit,1.);}';
 const mk=(t,s)=>{const h=gl.createShader(t);gl.shaderSource(h,s);gl.compileShader(h);if(!gl.getShaderParameter(h,gl.COMPILE_STATUS)){console.warn(gl.getShaderInfoLog(h));return null;}return h;};
 const v=mk(gl.VERTEX_SHADER,vs),f=mk(gl.FRAGMENT_SHADER,fs);if(!v||!f){gl=null;return false;}
 const p=gl.createProgram();gl.attachShader(p,v);gl.attachShader(p,f);gl.linkProgram(p);if(!gl.getProgramParameter(p,gl.LINK_STATUS)){gl=null;return false;}
 gl.useProgram(p);const U=n=>gl.getUniformLocation(p,n);LOC={VP:U('uVP'),M:U('uM'),R:U('uR'),Mul:U('uMul'),Fog:U('uFog'),Em:U('uEm'),P:gl.getAttribLocation(p,'aP'),N:gl.getAttribLocation(p,'aN'),C:gl.getAttribLocation(p,'aC'),E:gl.getAttribLocation(p,'aE')};
 [LOC.P,LOC.N,LOC.C,LOC.E].forEach(a=>gl.enableVertexAttribArray(a));gl.enable(gl.DEPTH_TEST);return true;}
function nrm(M){const r=[M[0],M[1],M[2],M[4],M[5],M[6],M[8],M[9],M[10]];for(let c=0;c<3;c++){const l=Math.hypot(r[c*3],r[c*3+1],r[c*3+2])||1;r[c*3]/=l;r[c*3+1]/=l;r[c*3+2]/=l;}return r;}
function render(list){gl.viewport(0,0,cv.width,cv.height);const f=S.fog;gl.clearColor(0.,0.,0.,0.);gl.clear(gl.COLOR_BUFFER_BIT|gl.DEPTH_BUFFER_BIT);
 gl.uniformMatrix4fv(LOC.VP,false,VP);gl.uniform3fv(LOC.Fog,f);let bound=null;
 for(const o of list){const m=o.m;if(!m.n)continue;if(!m.buf){m.buf=gl.createBuffer();gl.bindBuffer(gl.ARRAY_BUFFER,m.buf);gl.bufferData(gl.ARRAY_BUFFER,m.d,gl.STATIC_DRAW);}
  if(bound!==m){gl.bindBuffer(gl.ARRAY_BUFFER,m.buf);gl.vertexAttribPointer(LOC.P,3,gl.FLOAT,false,40,0);gl.vertexAttribPointer(LOC.N,3,gl.FLOAT,false,40,12);gl.vertexAttribPointer(LOC.C,3,gl.FLOAT,false,40,24);gl.vertexAttribPointer(LOC.E,1,gl.FLOAT,false,40,36);bound=m;}
  gl.uniformMatrix4fv(LOC.M,false,o.M);gl.uniformMatrix3fv(LOC.R,false,nrm(o.M));gl.uniform3fv(LOC.Mul,o.mul);gl.uniform1f(LOC.Em,o.em||0);gl.drawArrays(gl.TRIANGLES,0,m.n);}}
/* ---------- API ---------- */
window.Map3D={
 init(o){S.W=o.W;S.H=o.H;try{buildWorld(o);}catch(e){console.warn('Map3D build',e);S.ok=false;return false;}if(o.noGL)return true;if(!glInit()){S.ok=false;return false;}return true;},
 get ok(){return S.ok&&(!!gl||S.noGL);},
 snap(st){camUpdate(st,0,true);},
 frame(dt,T,st){camUpdate(st,dt,false);const list=collect(st,T);render(list);return cv;},
 skyCss:()=>S.sky.map(c=>'rgb('+c.map(v=>Math.round(v*255)).join(',')+')'),av:()=>S.av,dir:()=>S.dir,sx:i=>S.sxs[i],sy:i=>S.sys[i],bx:i=>S.bxs[i],by:i=>S.bys[i],hut:()=>S.hut,moving:()=>S.moving,
 _scene(st,T,snap){camUpdate(st,snap?0:.016,!!snap);return{list:collect(st,T),VP,fog:S.fog,W:S.W,H:S.H};},
 _S:S
};
})();
