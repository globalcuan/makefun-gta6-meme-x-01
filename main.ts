import { mkdirSync, copyFileSync, existsSync, writeFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { deflateSync } from 'node:zlib';

const bot = resolve(process.env.MAKEFUN_BOT_DIR || '/bot');
const out = resolve(process.env.MAKEFUN_OUTPUT_DIR || '/output');
if (!existsSync(resolve(bot, 'POST.json'))) { console.error(`Error: POST.json is missing from bot directory: ${bot}`); process.exit(1); }
mkdirSync(out, { recursive: true });
copyFileSync(resolve(bot, 'POST.json'), resolve(out, 'POST.json'));

const W=1024,H=1024,S=4, SW=W*S, SH=H*S;
const pix=new Uint8Array(SW*SH*4);
const col=(h:string):[number,number,number,number]=>{const s=h.replace('#','');return [parseInt(s.slice(0,2),16),parseInt(s.slice(2,4),16),parseInt(s.slice(4,6),16),255]};
function blend(x:number,y:number,c:string){x=Math.floor(x);y=Math.floor(y);if(x<0||y<0||x>=SW||y>=SH)return;const i=(y*SW+x)*4,a=col(c);pix[i]=a[0];pix[i+1]=a[1];pix[i+2]=a[2];pix[i+3]=255;}
function rect(x:number,y:number,w:number,h:number,c:string){for(let yy=Math.max(0,Math.floor(y*S));yy<Math.min(SH,Math.ceil((y+h)*S));yy++)for(let xx=Math.max(0,Math.floor(x*S));xx<Math.min(SW,Math.ceil((x+w)*S));xx++)blend(xx,yy,c);}
function ellipse(cx:number,cy:number,rx:number,ry:number,c:string){const x0=Math.max(0,Math.floor((cx-rx)*S)),x1=Math.min(SW,Math.ceil((cx+rx)*S)),y0=Math.max(0,Math.floor((cy-ry)*S)),y1=Math.min(SH,Math.ceil((cy+ry)*S));for(let y=y0;y<y1;y++)for(let x=x0;x<x1;x++){const dx=(x/S+.5/S-cx)/rx,dy=(y/S+.5/S-cy)/ry;if(dx*dx+dy*dy<=1)blend(x,y,c);}}
function roundRect(x:number,y:number,w:number,h:number,r:number,c:string){rect(x+r,y,w-2*r,h,c);rect(x,y+r,w,h-2*r,c);ellipse(x+r,y+r,r,r,c);ellipse(x+w-r,y+r,r,r,c);ellipse(x+r,y+h-r,r,r,c);ellipse(x+w-r,y+h-r,r,r,c);}
function polygon(points:number[][],c:string){const xs=points.map(p=>p[0]),ys=points.map(p=>p[1]),minX=Math.max(0,Math.floor(Math.min(...xs)*S)),maxX=Math.min(SW,Math.ceil(Math.max(...xs)*S)),minY=Math.max(0,Math.floor(Math.min(...ys)*S)),maxY=Math.min(SH,Math.ceil(Math.max(...ys)*S));for(let y=minY;y<maxY;y++)for(let x=minX;x<maxX;x++){const px=x/S+.5/S,py=y/S+.5/S;let inside=false;for(let i=0,j=points.length-1;i<points.length;j=i++){const [ax,ay]=points[i],[bx,by]=points[j];if(((ay>py)!==(by>py))&&(px<(bx-ax)*(py-ay)/(by-ay)+ax))inside=!inside;}if(inside)blend(x,y,c);}}
function line(x1:number,y1:number,x2:number,y2:number,width:number,c:string){const ax=x1*S,ay=y1*S,bx=x2*S,by=y2*S,rad=width*S/2,dx=bx-ax,dy=by-ay,l2=dx*dx+dy*dy;const x0=Math.max(0,Math.floor(Math.min(ax,bx)-rad)),x1b=Math.min(SW,Math.ceil(Math.max(ax,bx)+rad)),y0=Math.max(0,Math.floor(Math.min(ay,by)-rad)),y1b=Math.min(SH,Math.ceil(Math.max(ay,by)+rad));for(let yy=y0;yy<y1b;yy++)for(let xx=x0;xx<x1b;xx++){const t=l2?Math.max(0,Math.min(1,((xx+.5-ax)*dx+(yy+.5-ay)*dy)/l2)):0,qx=ax+t*dx,qy=ay+t*dy,ox=xx+.5-qx,oy=yy+.5-qy;if(ox*ox+oy*oy<=rad*rad)blend(xx,yy,c);}}
function strokePath(pts:number[][],w:number,c:string,closed=false){for(let i=1;i<pts.length;i++)line(...pts[i-1] as [number,number],...pts[i] as [number,number],w,c);if(closed&&pts.length>2)line(...pts[pts.length-1] as [number,number],...pts[0] as [number,number],w,c);}
function outlinePath(pts:number[][],radius:number,c:string){const r2=(radius*S)**2,minX=Math.max(0,Math.floor((Math.min(...pts.map(p=>p[0]))-radius)*S)),maxX=Math.min(SW,Math.ceil((Math.max(...pts.map(p=>p[0]))+radius)*S)),minY=Math.max(0,Math.floor((Math.min(...pts.map(p=>p[1]))-radius)*S)),maxY=Math.min(SH,Math.ceil((Math.max(...pts.map(p=>p[1]))+radius)*S));for(let y=minY;y<maxY;y++)for(let x=minX;x<maxX;x++){const px=(x+.5)/S,py=(y+.5)/S;let d2=Infinity;for(let i=0;i<pts.length;i++){const a=pts[i],b=pts[(i+1)%pts.length],dx=b[0]-a[0],dy=b[1]-a[1],l2=dx*dx+dy*dy,t=l2?Math.max(0,Math.min(1,((px-a[0])*dx+(py-a[1])*dy)/l2)):0,ox=px-(a[0]+t*dx),oy=py-(a[1]+t*dy);d2=Math.min(d2,(ox*ox+oy*oy)*S*S);if(d2<=r2)break;}if(d2<=r2)blend(x,y,c);}}
// SVG path parser/flattener for M/L/H/V/Q/C/A/Z, absolute and relative commands.
function parsePath(d:string,tx:number,ty:number,k:number){const toks=d.match(/[a-zA-Z]|[-+]?(?:\d*\.)?\d+(?:[eE][-+]?\d+)?/g)||[];let i=0,cmd='',x=0,y=0,sx=0,sy=0,paths:number[][][]=[[]];const curr=()=>paths[paths.length-1];const val=()=>Number(toks[i++]);const point=(a:number,b:number)=>[tx+a*k,ty+b*k];while(i<toks.length){if(/[a-z]/i.test(toks[i]))cmd=toks[i++];if(!cmd)break;const rel=cmd===cmd.toLowerCase(),u=cmd.toUpperCase();if(u==='Z'){x=sx;y=sy;continue;}if(u==='M'||u==='L'){const nx=val(),ny=val();x=rel?x+nx:nx;y=rel?y+ny:ny;if(u==='M'){if(curr().length)paths.push([]);curr().push(point(x,y));sx=x;sy=y;cmd=rel?'l':'L';}else curr().push(point(x,y));}else if(u==='H'){let a=val();x=rel?x+a:a;curr().push(point(x,y));}else if(u==='V'){let a=val();y=rel?y+a:a;curr().push(point(x,y));}else if(u==='Q'){let ax=val(),ay=val(),ex=val(),ey=val();if(rel){ax+=x;ay+=y;ex+=x;ey+=y;}const ox=x,oy=y;for(let z=1;z<=16;z++){const t=z/16,q=1-t;curr().push(point(q*q*ox+2*q*t*ax+t*t*ex,q*q*oy+2*q*t*ay+t*t*ey));}x=ex;y=ey;}else if(u==='C'){let a=val(),b=val(),c=val(),e=val(),f=val(),g=val();if(rel){a+=x;b+=y;c+=x;e+=y;f+=x;g+=y;}const ox=x,oy=y;for(let z=1;z<=20;z++){const t=z/20,q=1-t;curr().push(point(q*q*q*ox+3*q*q*t*a+3*q*t*t*c+t*t*t*f,q*q*q*oy+3*q*q*t*b+3*q*t*t*e+t*t*t*g));}x=f;y=g;}else if(u==='A'){const rx=val(),ry=val();val();val();val();let ex=val(),ey=val();if(rel){ex+=x;ey+=y;}const ox=x,oy=y;const n=Math.max(12,Math.ceil(Math.hypot(ex-ox,ey-oy)*2));for(let z=1;z<=n;z++){const t=z/n;curr().push(point(ox+(ex-ox)*t,oy+(ey-oy)*t));}x=ex;y=ey;}else break;}return paths;}
function path(d:string,t:{x:number,y:number,s:number},fill:string|null,sw=0,sc='#191419'){for(const p of parsePath(d,t.x,t.y,t.s)){if(fill&&p.length>2)polygon(p,fill);if(sw)strokePath(p,sw,sc,true);}}
const font:Record<string,string[]>={A:['01110','10001','10001','11111','10001','10001','10001'],B:['11110','10001','10001','11110','10001','10001','11110'],C:['01111','10000','10000','10000','10000','10000','01111'],D:['11110','10001','10001','10001','10001','10001','11110'],E:['11111','10000','10000','11110','10000','10000','11111'],F:['11111','10000','10000','11110','10000','10000','10000'],G:['01111','10000','10000','10111','10001','10001','01111'],H:['10001','10001','10001','11111','10001','10001','10001'],I:['11111','00100','00100','00100','00100','00100','11111'],J:['00111','00010','00010','00010','10010','10010','01100'],K:['10001','10010','10100','11000','10100','10010','10001'],L:['10000','10000','10000','10000','10000','10000','11111'],M:['10001','11011','10101','10101','10001','10001','10001'],N:['10001','11001','10101','10011','10001','10001','10001'],O:['01110','10001','10001','10001','10001','10001','01110'],P:['11110','10001','10001','11110','10000','10000','10000'],Q:['01110','10001','10001','10001','10101','10010','01101'],R:['11110','10001','10001','11110','10100','10010','10001'],S:['01111','10000','10000','01110','00001','00001','11110'],T:['11111','00100','00100','00100','00100','00100','00100'],U:['10001','10001','10001','10001','10001','10001','01110'],V:['10001','10001','10001','10001','10001','01010','00100'],W:['10001','10001','10001','10101','10101','10101','01010'],X:['10001','10001','01010','00100','01010','10001','10001'],Y:['10001','10001','01010','00100','00100','00100','00100'],Z:['11111','00001','00010','00100','01000','10000','11111'],0:['01110','10001','10011','10101','11001','10001','01110'],1:['00100','01100','00100','00100','00100','00100','01110'],2:['01110','10001','00001','00010','00100','01000','11111'],3:['11110','00001','00001','01110','00001','00001','11110'],4:['00010','00110','01010','10010','11111','00010','00010'],5:['11111','10000','10000','11110','00001','00001','11110'],6:['01110','10000','10000','11110','10001','10001','01110'],7:['11111','00001','00010','00100','01000','01000','01000'],8:['01110','10001','10001','01110','10001','10001','01110'],9:['01110','10001','10001','01111','00001','00001','01110'],'.':['00000','00000','00000','00000','00000','00110','00110'],'%':['11001','11010','00100','01000','10110','00110','00000'],"'":['00100','00100','00000','00000','00000','00000','00000'],'-':['00000','00000','00000','11111','00000','00000','00000'],'!':['00100','00100','00100','00100','00100','00000','00100'],':':['00000','00110','00110','00000','00110','00110','00000']};
function textWidth(t:string,scale:number){return Math.max(0,t.length*6*scale-scale);}
function textDraw(t:string,cx:number,y:number,scale:number,color:string,outline=0){const str=t.toUpperCase(),x0=cx-textWidth(str,scale)/2;function draw(colr:string,extra:number){let x=x0;for(const ch of str){const glyph=font[ch]||font[' '];if(glyph)for(let yy=0;yy<7;yy++)for(let xx=0;xx<5;xx++)if(glyph[yy][xx]==='1')rect(x+xx*scale-extra,y+yy*scale-extra,scale+2*extra,scale+2*extra,colr);x+=6*scale;}}if(outline)draw('#09070f',outline);draw(color,0);}
// Sunset wall gradient
for(let y=0;y<844;y++){const t=y/844,r=Math.round(36+143*t),g=Math.round(22+31*t),b=Math.round(73+51*t);rect(0,y,1024,1,`#${r.toString(16).padStart(2,'0')}${g.toString(16).padStart(2,'0')}${b.toString(16).padStart(2,'0')}`);}
rect(0,844,1024,180,'#21182f');rect(0,841,1024,4,'#66304e');
// television and screen
roundRect(190,128,644,464,22,'#100f1d');roundRect(207,145,610,420,12,'#292538');roundRect(224,162,576,382,6,'#103b48');
// screen content
ellipse(512,362,205,125,'#145061');rect(241,440,542,80,'#102e3b');
textDraw('GTA VI',512,254,12,'#f4e9e7',1);
roundRect(274,390,476,26,11,'#ffffff');roundRect(277,393,470,20,8,'#070b13');roundRect(280,396,462,14,6,'#c41c83');rect(736,396,6,14,'#070b13');
textDraw('INSTALLING 99%',512,430,5,'#ffffff',1);
roundRect(426,151,172,27,13,'#c41c83');textDraw('make.fun',512,158,2,'#ffffff');
// caption top
txt: { };
textDraw('WAITED 13 YEARS FOR GTA 6',512,54,6,'#ffffff',2);
// Ghost body artwork with requested group transform (screen placement + tile scale)
const gx=240,gy=390,gs=16;const gt={x:gx+3.858*gs,y:gy+3.202*gs,s:.79*gs};
ellipse(512,837,130,16,'#100d1b');
const ghostBody='M6.2 17 C4.1 15.8 5.4 12.8 6.5 11.5 C6.1 6.8 10.3 3.8 14.4 3.8 C18.9 3.8 22.6 7.1 22.6 12.8 L22.6 17.6 C24.5 17.9 25.8 19.5 24.4 21.1 C23.8 21.8 23 22.1 22.6 22.2 L22.6 25 C22.6 26.5 21.5 27.6 20 27.6 C17.9 27.6 16.1 27.4 14.5 26.4 C13 27.4 10.9 27.6 9 27.6 C7.4 27.6 6.2 26.4 6.2 25 L6.2 23.5 C4.9 24.2 2.7 23.7 2.6 21.8 C2.5 19.8 4.1 18 6.2 17 Z';
path(ghostBody,gt,'#ffffff');
const ghostOutline=parsePath(ghostBody,gt.x,gt.y,gt.s)[0];outlinePath(ghostOutline,1.7*gt.s,'#191419');
path('M6.3 24.1v-2.5m8 5.8v-1.5',gt,null,1.25*gt.s,'#191419');
// Official magenta coin and white hand, layered above the body outline and detail lines.
const coinX=26.5,coinY=13.4;
ellipse(gt.x+coinX*gt.s,gt.y+coinY*gt.s,5.5*gt.s,5.5*gt.s,'#191419');
ellipse(gt.x+coinX*gt.s,gt.y+coinY*gt.s,3.8*gt.s,3.8*gt.s,'#c41c83');
path('M28 10.1L28.8 11.7L30.6 12L29.3 13.3L29.6 15.1L28 14.2L26.4 15.1L26.7 13.3L25.4 12L27.2 11.7Z',gt,'#ffffff');
ellipse(gt.x+24.9*gt.s,gt.y+19.6*gt.s,4*gt.s,4*gt.s,'#191419');
ellipse(gt.x+24.9*gt.s,gt.y+19.6*gt.s,2.3*gt.s,2.3*gt.s,'#ffffff');
// Sparkle eyes are the topmost ghost details.
path('M11.4 9.8L11.8 11.2L13.2 11.6L11.8 12L11.4 13.4L11 12L9.6 11.6L11 11.2z',gt,'#191419');path('M17.5 9L17.9 10.4L19.3 10.8L17.9 11.2L17.5 12.6L17.1 11.2L15.7 10.8L17.1 10.4z',gt,'#191419');
// Controller held in front, overlapping only the ghost's lower edge
roundRect(417,775,190,78,22,'#10121b');roundRect(425,782,174,59,17,'#292936');rect(457,797,10,31,'#11121c');rect(447,807,31,10,'#11121c');ellipse(557,803,9,9,'#c41c83');ellipse(579,817,9,9,'#c41c83');
// coin stack on right floor
function coin(x:number,y:number,r:number){ellipse(x,y,r,r*.42,'#191419');ellipse(x,y-5,r,r*.42,'#c41c83');ellipse(x,y-7,r*.72,r*.28,'#ee55ae');polygon([[x,y-13],[x+3,y-9],[x+8,y-8],[x+4,y-4],[x+5,y+1],[x,y-2],[x-5,y+1],[x-4,y-4],[x-8,y-8],[x-3,y-9]],'#ffffff');}
coin(758,828,30);coin(811,817,25);coin(785,793,26);
textDraw('MY AGENT GOT PAID',512,887,8,'#ffffff',2);textDraw('BEFORE IT FINISHED INSTALLING',512,951,5,'#ffffff',2);
// Downsample 4x4 samples to final RGBA
const raw=Buffer.alloc((W*4+1)*H);for(let y=0;y<H;y++){const row=y*(W*4+1);raw[row]=0;for(let x=0;x<W;x++){let rr=0,gg=0,bb=0;for(let sy=0;sy<S;sy++)for(let sx=0;sx<S;sx++){const i=(((y*S+sy)*SW)+(x*S+sx))*4;rr+=pix[i];gg+=pix[i+1];bb+=pix[i+2];}const o=row+1+x*4;raw[o]=rr/16;raw[o+1]=gg/16;raw[o+2]=bb/16;raw[o+3]=255;}}
function crc32(b:Buffer){let c=0xffffffff;for(const v of b){c^=v;for(let k=0;k<8;k++)c=(c>>>1)^((c&1)?0xedb88320:0);}return (c^0xffffffff)>>>0;}
function chunk(type:string,data:Buffer){const name=Buffer.from(type),len=Buffer.alloc(4),crc=Buffer.alloc(4);len.writeUInt32BE(data.length);crc.writeUInt32BE(crc32(Buffer.concat([name,data])));return Buffer.concat([len,name,data,crc]);}
const ih=Buffer.alloc(13);ih.writeUInt32BE(W,0);ih.writeUInt32BE(H,4);ih[8]=8;ih[9]=6;
const png=Buffer.concat([Buffer.from([137,80,78,71,13,10,26,10]),chunk('IHDR',ih),chunk('IDAT',deflateSync(raw,{level:6})),chunk('IEND',Buffer.alloc(0))]);writeFileSync(resolve(out,'meme.png'),png);
