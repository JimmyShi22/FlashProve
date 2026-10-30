(function(){
const DATA = JSON.parse(document.getElementById('audit-data').textContent);
// decl row: [key, kindIdx, fileIdx, line, end, blockEnd, docStart(0=none), emb (last embedded line), 1 for a theorem whose list of axioms in the page's compile record is within the standard three (0 otherwise), displayName('' = key)]
// file row: [path as shown, first 12 hex digits of its sha256, number of lines, embedded segments, a label for a proposed file ('' for a file of the upload)]
const FILES = DATA.files, DL = DATA.decls, KINDS = DATA.kinds, LINKS = DATA.links, CUT = DATA.cut;
const IDX = Object.create(null);            // prototype-free: a Lean name such as `constructor` must not hit Object.prototype
for(let i=0;i<DL.length;i++) IDX[DL[i][0]] = i;
const KW = new Set(["theorem", "lemma", "def", "abbrev", "structure", "class", "inductive", "axiom", "opaque", "instance", "where", "extends", "fun", "let", "have", "by", "match", "with", "if", "then", "else", "do", "return", "namespace", "end", "open", "variable", "import", "deriving", "noncomputable", "private", "protected", "at", "in", "from", "show", "calc", "sorry", "section", "universe", "set_option", "attribute", "local", "scoped", "partial", "unsafe", "mutual", "termination_by", "decreasing_by", "obtain", "intro", "intros", "exact", "refine", "apply", "rw", "simp", "constructor", "rcases", "cases", "induction", "use", "norm_num", "omega", "decide", "ring", "field_simp", "linarith", "nlinarith", "positivity", "push_cast", "exact_mod_cast", "rintro", "rfl", "trivial", "ext", "funext", "congr", "specialize", "rename_i", "suffices", "change", "unfold", "dsimp", "simpa", "aesop", "gcongr", "contradiction", "exfalso", "left", "right", "subst", "clear", "generalize", "symm", "trans", "norm_cast", "zify", "qify", "lift", "choose", "classical", "infer_instance", "hiding", "export", "example", "for", "unless", "instance", "simp_all", "native_decide", "rename", "using", "only", "this", "fun", "Type", "Prop", "Sort", "True", "False"]);
const DECLKW = new Set(['theorem','lemma','def','abbrev','structure','class','inductive','axiom','opaque','instance']);
const TY = new Set(['ℕ','ℝ','ℚ','ℤ','Prop','Type','Sort','Bool','Nat','Int','Rat','Real','Fin','Finset','Fintype','Set','List','Array','ByteArray','Option','Field','DecidableEq','Nonempty','ZMod','IO','String','UInt32','UInt64','UInt8','Unit','Sum','Prod','Subtype','True','False']);
const SYM = "≤≥≠∀∃∈∉⊆⊂⊇⊗⊓⊔→←↔⇒⇐⇔∧∨¬⟨⟩∑∏√·×∘∣λ∞∂∫≈≡∅∩∪∖⊥⊤↑↓⁻¹²³⁴⁵⁶⁷⁸⁹⁰⁽⁾ᵀ∙⬝•‖▸⟶↦⊢…—–⦃⦄‹›«»≃≅⊕⊖∤≺≻⌊⌋⌈⌉∎⋯∐⋃⋂≪≫∥∋∌⊄⊈⊊⊋∶◁▷⊣‑’‘“”";
const DEFK = new Set(['def','abbrev','structure','class','inductive','instance','opaque','axiom']);
function esc(s){ return s.replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;'); }
function escAttr(s){ return esc(s).replace(/"/g,'&quot;'); }
const ASCII_START=/[A-Za-z_]/, ASCII_ID=/[A-Za-z0-9_'!?]/;
function isIdStart(c){ return ASCII_START.test(c) || (c>='\u00C0' && !SYM.includes(c)); }
function isId(c){ return ASCII_ID.test(c) || (c>='\u00C0' && !SYM.includes(c)); }
// tokenizer for COLOURS only (links come from the precomputed table): [start, end, cssClass], sorted, non-overlapping
function tokenize(code){
  const toks=[]; let i=0, n=code.length, lastDeclKwEnd=-1;
  while(i<n){
    const c=code[i];
    if(c==='/' && code.startsWith('/-',i)){
      const isDoc=code.startsWith('/--',i)||code.startsWith('/-!',i); let depth=0, j=i;
      while(j<n){ if(code.startsWith('/-',j)){depth++; j+=2;} else if(code.startsWith('-/',j)){depth--; j+=2; if(depth===0) break;} else j++; }
      toks.push([i,j,isDoc?'lean-doc':'lean-comment']); i=j; continue; }
    if(c==='-' && code.startsWith('--',i)){ let j=code.indexOf('\n',i); if(j<0) j=n; toks.push([i,j,'lean-comment']); i=j; continue; }
    if(c==='"'){ let j=i+1; while(j<n && code[j]!=='"'){ if(code[j]==='\\') j++; j++; } j=Math.min(j+1,n); toks.push([i,j,'lean-str']); i=j; continue; }
    if(c==='@' && code.startsWith('@[',i)){ let j=code.indexOf(']',i); j=(j<0)?n:j+1; toks.push([i,j,'lean-attr']); i=j; continue; }
    if(c>='0' && c<='9' && (i===0 || !isId(code[i-1]))){ let j=i; while(j<n && /[0-9.]/.test(code[j])) j++; toks.push([i,j,'lean-num']); i=j; continue; }
    if(isIdStart(c)){
      let j=i; while(j<n && (isId(code[j]) || (code[j]==='.' && j+1<n && isIdStart(code[j+1])))) j++;
      if(j===i){ i++; continue; }                         // guarantee progress
      const tok=code.slice(i,j);
      if(KW.has(tok)){ toks.push([i,j,'lean-kw']); if(DECLKW.has(tok)) lastDeclKwEnd=j; }
      else if(lastDeclKwEnd>=0 && code.slice(lastDeclKwEnd,i).trim()===''){ toks.push([i,j,'lean-decl']); lastDeclKwEnd=-1; }
      else if(TY.has(tok)) toks.push([i,j,'lean-ty']);
      i=j; continue; }
    i++;
  }
  return toks;
}
const lineCache=[];
function fileMap(fi){ if(!lineCache[fi]){ const m=new Map(); for(const seg of FILES[fi][3]){ const L=seg[1].split('\n'); for(let k=0;k<L.length;k++) m.set(seg[0]+k, L[k]); } lineCache[fi]=m; } return lineCache[fi]; }
function lineHTML(s, spans, lk, cutTotal){
  const n=s.length, cuts=new Set([0,n]);
  for(const sp of spans){ cuts.add(sp[0]); cuts.add(sp[1]); }
  for(let q=0;q<lk.length;q+=3){ if(lk[q]<n){ cuts.add(lk[q]); cuts.add(Math.min(lk[q]+lk[q+1],n)); } }
  const pts=[...cuts].sort((x,y)=>x-y); let html='', si=0;
  for(let p=0;p+1<pts.length;p++){ const a=pts[p], b=pts[p+1]; if(b<=a) continue;
    while(si<spans.length && spans[si][1]<=a) si++;
    const cls=(si<spans.length && spans[si][0]<=a)?spans[si][2]:'';
    let tgt=-1; for(let q=0;q<lk.length;q+=3){ if(lk[q]<=a && a<lk[q]+lk[q+1]){ tgt=lk[q+2]; break; } }
    let piece=esc(s.slice(a,b)); if(cls) piece='<span class="'+cls+'">'+piece+'</span>';
    if(tgt>=0) piece='<span class="ident-link" data-name="'+escAttr(DL[tgt][0])+'">'+piece+'</span>';
    html+=piece; }
  if(cutTotal) html+='<span class="cut-note"> ⋯ '+(cutTotal-n)+' more characters of this line are not embedded</span>';
  return html;
}
// lines a..b of file fi (all embedded) -> array of per-line HTML (no wrappers)
function renderRange(fi, a, b){
  const m=fileMap(fi), lines=[]; for(let ln=a; ln<=b; ln++) lines.push(m.has(ln)?m.get(ln):'');
  const toks=tokenize(lines.join('\n')), lk=LINKS[fi]||{}, ct=CUT[fi]||{}, out=[]; let off=0, ti=0;
  for(let r=0;r<lines.length;r++){ const s=lines[r], L0=off, L1=off+s.length, spans=[];
    while(ti<toks.length && toks[ti][1]<=L0) ti++;
    for(let t=ti;t<toks.length && toks[t][0]<L1;t++){ const c0=Math.max(toks[t][0],L0)-L0, c1=Math.min(toks[t][1],L1)-L0; if(c1>c0) spans.push([c0,c1,toks[t][2]]); }
    out.push(lineHTML(s, spans, lk[a+r]||[], ct[a+r]||0)); off=L1+1; }
  return out;
}
const DOC_SKIP=8;   // a docstring of at least this many lines is scrolled past when a declaration opens (it stays above, one scroll away)
function markOf(d){ return (d[6] && d[3]-d[6]>=DOC_SKIP)?d[3]:-1; }
function wrapLines(htmls, a, hlA, hlB, withLn, mark){ let h='';
  for(let k=0;k<htmls.length;k++){ const ln=a+k; h+='<div class="cl'+((ln>=hlA&&ln<=hlB)?' hl-line':'')+(ln===mark?' stmt-first':'')+'">'+(withLn?'<span class="ln">'+ln+'</span>':'')+(htmls[k]||'&#8203;')+'</div>'; }
  return h; }
function restNote(d){ if(d[7]>=d[5]) return ''; const thm=!DEFK.has(KINDS[d[1]]);
  return '<div class="gap-note">⋯ lines '+(d[7]+1)+'–'+d[5]+' of '+esc(FILES[d[2]][0])+' ('+(thm?'the proof':'the rest of this table of literals')+') are not embedded in this page</div>'; }
function renderDecl(i, mode, withLn){ // mode: 'stmt' | 'proof'
  const d=DL[i], a=d[6]||d[3], b=(mode==='stmt')?Math.min(d[4],d[7]):d[7];
  return wrapLines(renderRange(d[2],a,b), a, d[3], Math.min(d[4],d[7]), withLn, markOf(d)) + ((mode==='proof'||DEFK.has(KINDS[d[1]]))?restNote(d):''); }
function renderFile(fi, i){ const d=(i>=0)?DL[i]:null, segs=FILES[fi][3]; let h='', prev=0;
  for(const seg of segs){ const n=seg[1].split('\n').length, a=seg[0], b=a+n-1;
    if(a>prev+1) h+='<div class="gap-note">⋯ lines '+(prev+1)+'–'+(a-1)+' are not embedded</div>';
    h+=wrapLines(renderRange(fi,a,b), a, d?d[3]:-1, d?Math.min(d[4],d[7]):-1, true); prev=b; }
  if(prev<FILES[fi][2]) h+='<div class="gap-note">⋯ lines '+(prev+1)+'–'+FILES[fi][2]+' are not embedded</div>';
  return h; }
function dispName(d){ return d[9]||d[0]; }
function chips(d){ let h='';
  if(FILES[d[2]][4]) h+='<span class="chip chip-other" title="a proposed Lean file; not a file of the upload">'+esc(FILES[d[2]][4])+' · not part of the upload</span>';
  if(d[8]) h+='<span class="chip chip-std" title="what #print axioms printed when the proposed files were compiled: none beyond propext, Classical.choice, Quot.sound">proved · standard axioms only</span>';
  return h; }
// ---- statements in rows: a piece of one embedded line, columns [c0, c1) of line ln of file fi, with the colours and links of the panel
function fragHTML(fi, ln, c0, c1){
  const m=fileMap(fi), s=m.has(ln)?m.get(ln):'', toks=tokenize(s), spans=[], lk=(LINKS[fi]||{})[ln]||[], lk2=[];
  for(const t of toks){ const a=Math.max(t[0],c0), b=Math.min(t[1],c1); if(b>a) spans.push([a-c0,b-c0,t[2]]); }
  for(let q=0;q<lk.length;q+=3){ if(lk[q]>=c0 && lk[q]+lk[q+1]<=c1) lk2.push(lk[q]-c0, lk[q+1], lk[q+2]); }
  return lineHTML(s.slice(c0,c1), spans, lk2, 0);
}
document.querySelectorAll('.sbs').forEach(box=>{ const i=IDX[box.dataset.decl]; if(i===undefined) return;
  box.querySelectorAll('.fl').forEach(el=>{ el.innerHTML=fragHTML(DL[i][2], +el.dataset.l, +el.dataset.a, +el.dataset.b)||'&#8203;'; }); });
// ---- panel
const col=document.getElementById('lean-col'), body=document.getElementById('lean-body'), fileEl=document.getElementById('lean-file'), meta=document.getElementById('lean-meta');
const btnBack=document.getElementById('btn-back'), btnClose=document.getElementById('btn-close'), btnProof=document.getElementById('btn-proof'), btnFile=document.getElementById('btn-file');
let hist=[], current=null, mode='stmt';
function show(name, push){
  const i=IDX[name]; if(i===undefined){ body.innerHTML='<div class="placeholder">Declaration not embedded: '+esc(String(name))+'</div>'; return; }
  const d=DL[i], kind=KINDS[d[1]], f=FILES[d[2]];
  if(push && current!==null && current!==name) hist.push(current);
  current=name; col.classList.add('open');
  fileEl.textContent=f[0]+':'+d[3];
  meta.style.display='block';
  const hasMore=d[7]>Math.min(d[4],d[7]) && !DEFK.has(kind);
  meta.innerHTML='<b>'+esc(dispName(d))+'</b> &nbsp;·&nbsp; '+esc(kind)+' &nbsp;·&nbsp; lines '+d[3]+'–'+d[4]+(d[5]>d[4]?' ('+(DEFK.has(kind)?'body':'proof')+' to '+d[5]+')':'')
    +(chips(d)?' &nbsp;·&nbsp; '+chips(d):'')+' &nbsp;·&nbsp; <span style="color:#555">sha256 '+esc(f[1])+'…</span>';
  btnProof.style.display=hasMore?'':'none'; btnProof.classList.toggle('on',mode==='proof'); btnFile.classList.toggle('on',mode==='file');
  if(mode==='file') body.innerHTML=renderFile(d[2], i);
  else body.innerHTML=renderDecl(i, (mode==='proof'||DEFK.has(kind))?'proof':'stmt', true);
  body.scrollTop=0;
  if(mode!=='file'){ const st=body.querySelector('.stmt-first'); if(st && st.getBoundingClientRect){ body.scrollTop=Math.max(0, st.getBoundingClientRect().top-body.getBoundingClientRect().top-44); } }
  if(mode==='file'){ const first=body.querySelector('.hl-line'); if(first && first.scrollIntoView) first.scrollIntoView({block:'center'}); }
  btnBack.disabled=hist.length===0;
  document.querySelectorAll('.lean-link.active').forEach(e=>e.classList.remove('active'));
  document.querySelectorAll('.lean-link[data-name="'+((window.CSS&&CSS.escape)?CSS.escape(name):name)+'"]').forEach(e=>e.classList.add('active'));
  if(push){ try{ history.replaceState(null,'','#'+encodeURIComponent(name)); }catch(e){} }
}
btnBack.onclick=()=>{ if(hist.length){ const p=hist.pop(); show(p,false); btnBack.disabled=hist.length===0; } };
btnClose.onclick=()=>{ col.classList.remove('open'); killAll(); document.querySelectorAll('.lean-link.active').forEach(e=>e.classList.remove('active')); };
btnProof.onclick=()=>{ mode=(mode==='proof')?'stmt':'proof'; if(current!==null) show(current,false); };
btnFile.onclick=()=>{ mode=(mode==='file')?'stmt':'file'; if(current!==null) show(current,false); };
document.addEventListener('keydown',e=>{ if(e.key==='Escape'){ killAll(); col.classList.remove('open'); } });
document.addEventListener('click',e=>{ const b=e.target.closest('.lean-link[data-name], .name-link[data-name], .sbs .ident-link[data-name]'); if(b){ killAll(); show(b.dataset.name,true); } });
// ---- hover explorer: a stack of tooltips; level 0 anchors on any Lean link or identifier in the panel, level k+1 on an identifier inside
// tooltip k.  Click anywhere in a tooltip to open that declaration in the panel.  (Timing and scroll rules are the skill's; do not change.)
const TIP_LINES=400;
let tips=[], tipTimer=null, tipOpenTimer=null, lastWheel=0, insideTip=false;
function killTips(level){ level=level||0; while(tips.length>level){ tips.pop().el.remove(); } if(level===0) insideTip=false; }
function killAll(){ if(tipTimer) clearTimeout(tipTimer); if(tipOpenTimer) clearTimeout(tipOpenTimer); killTips(0); }
function scheduleKill(){ if(tipTimer) clearTimeout(tipTimer); tipTimer=setTimeout(()=>killTips(0),260); }
function cancelKill(){ if(tipTimer) clearTimeout(tipTimer); tipTimer=null; }
function tipHTML(name){
  const i=IDX[name], d=DL[i], kind=KINDS[d[1]], full=DEFK.has(kind);
  const a=d[6]||d[3]; let b=full?d[7]:Math.min(d[4],d[7]); let more='';
  if(b-a+1>TIP_LINES){ more='… '+(b-a+1-TIP_LINES)+' more lines — click to open in the panel'; b=a+TIP_LINES-1; }
  const kindLbl=kind+(full?'':' (statement)');
  return '<div class="mt-header">'+esc(dispName(d))+' <span class="mt-file">'+esc(kindLbl)+' · '+esc(FILES[d[2]][0])+':'+d[3]+(FILES[d[2]][4]?' · '+esc(FILES[d[2]][4]).toUpperCase():'')+' · hover an identifier to drill down, click to open</span></div>'
    +'<div class="mt-code">'+wrapLines(renderRange(d[2],a,b), a, -1, -1, false, markOf(d))+(more?'<div class="gap-note">'+esc(more)+'</div>':'')+(full&&!more?restNote(d):'')+'</div>';
}
function placeTip(t, anchor){
  const r=anchor.getBoundingClientRect(), W=window.innerWidth, Hh=window.innerHeight;
  t.style.left='0px'; t.style.top='0px'; t.style.maxWidth=Math.min(900,W-16)+'px';
  const tr=t.getBoundingClientRect(); const left=Math.max(8,Math.min(r.left,W-tr.width-8)); let top=r.bottom+6;
  if(top+tr.height>Hh-8){ const above=r.top-6-tr.height; top=(above>=8)?above:Math.max(8,Hh-8-tr.height); }
  t.style.left=left+'px'; t.style.top=top+'px';
}
function openTip(anchor, name, level){
  if(IDX[name]===undefined) return; cancelKill();
  if(tips.length>level && tips[level].name===name){ killTips(level+1); return; }
  killTips(level);
  const t=document.createElement('div'); t.className='mini-tooltip'; t.dataset.level=level; t.innerHTML=tipHTML(name);
  document.body.appendChild(t); placeTip(t, anchor); tips.push({el:t,name:name,anchor:anchor});
  if(t.scrollHeight>t.clientHeight+2){ const h=t.querySelector('.mt-header'); if(h) h.insertAdjacentHTML('beforeend',' <span class="mt-scroll">· scroll for more</span>'); }
  const st=t.querySelector('.stmt-first');   // long docstring: open at the statement; the docstring is one scroll up
  if(st){ const h=t.querySelector('.mt-header'), hh=h?h.offsetHeight:0; t.scrollTop=Math.max(0, st.getBoundingClientRect().top-t.getBoundingClientRect().top-hh-34);
    if(h && t.scrollTop>0) h.insertAdjacentHTML('beforeend',' <span class="mt-scroll">· docstring above</span>'); }
  // wheel handling is left to the browser (overscroll-behavior: contain); never preventDefault on wheel events
  t.addEventListener('wheel',()=>{ lastWheel=Date.now(); },{passive:true});
  t.addEventListener('mouseenter',()=>{ insideTip=true; });
  t.addEventListener('mouseleave',()=>{ insideTip=false; });
  t.addEventListener('mouseenter',cancelKill);
  t.addEventListener('mouseleave',scheduleKill);
  t.addEventListener('mouseover',e=>{ const il=e.target.closest('.ident-link'); if(tipOpenTimer) clearTimeout(tipOpenTimer); if(Date.now()-lastWheel<400) return;
    if(il){ tipOpenTimer=setTimeout(()=>openTip(il, il.dataset.name, level+1),140); } else { tipOpenTimer=setTimeout(()=>killTips(level+1),300); } });
  t.addEventListener('click',e=>{ const il=e.target.closest('.ident-link'); const nm=il?il.dataset.name:name; killAll(); show(nm,true); e.stopPropagation(); });
}
document.addEventListener('mouseover',e=>{ if(e.target.closest('.mini-tooltip')) return;
  const a=e.target.closest('.lean-link[data-name], .ident-link[data-name], .name-link[data-name]'); if(tipOpenTimer) clearTimeout(tipOpenTimer);
  if(a){ cancelKill(); tipOpenTimer=setTimeout(()=>openTip(a, a.dataset.name, 0), a.classList.contains('ident-link')?120:200); } });
document.addEventListener('mouseout',e=>{ if(e.target.closest('.mini-tooltip')) return;
  const a=e.target.closest('.lean-link[data-name], .ident-link[data-name], .name-link[data-name]'); if(a){ if(tipOpenTimer) clearTimeout(tipOpenTimer); scheduleKill(); } });
body.addEventListener('click',e=>{ const il=e.target.closest('.ident-link'); if(il){ e.preventDefault(); killAll(); show(il.dataset.name,true); } });
document.addEventListener('scroll',e=>{ const el=e.target; if(el&&el.nodeType===1&&el.closest('.mini-tooltip')) return; if(insideTip) return; killTips(0); },true);
document.addEventListener('keydown',e=>{ if(e.key==='Escape') killAll(); });
// ---- index of embedded declarations
const list=document.getElementById('decl-list'), search=document.getElementById('search');
const order=DL.map((d,i)=>i).sort((x,y)=>DL[x][2]===DL[y][2]?DL[x][3]-DL[y][3]:(FILES[DL[x][2]][0]<FILES[DL[y][2]][0]?-1:1));
function renderList(q){ q=(q||'').toLowerCase().trim(); let h='', n=0, total=0;
  for(const i of order){ const d=DL[i], nm=dispName(d), f=FILES[d[2]][0]; if(q && !(nm.toLowerCase().includes(q)||f.toLowerCase().includes(q))) continue; total++; if(n>=400) continue; n++;
    h+='<div><span class="k">'+esc(KINDS[d[1]])+'</span><a data-name="'+escAttr(d[0])+'">'+esc(nm)+'</a><span class="f">'+esc(f)+':'+d[3]+'</span></div>'; }
  if(total>n) h+='<div style="color:#999">… '+(total-n)+' more; refine the filter</div>';
  list.innerHTML=h||'<div style="color:#999">no match</div>'; }
if(list){ renderList(''); search.addEventListener('input',()=>renderList(search.value));
  list.addEventListener('click',e=>{ const a=e.target.closest('a[data-name]'); if(a) show(a.dataset.name,true); }); }
// deep link
if(location.hash.length>1){ let nm=''; try{ nm=decodeURIComponent(location.hash.slice(1)); }catch(e){}
  if(IDX[nm]!==undefined){ show(nm,false); const c=document.getElementById('card-'+nm); if(c && c.scrollIntoView) c.scrollIntoView({block:'center'}); } }
window.__viewer={DL:DL, FILES:FILES, KINDS:KINDS, IDX:IDX, LINKS:LINKS, CUT:CUT, tokenize:tokenize, renderRange:renderRange, fragHTML:fragHTML, fileMap:fileMap, renderDecl:renderDecl, renderFile:renderFile, tipHTML:tipHTML, show:show,
  declSpan:function(name){ const i=IDX[name]; if(i===undefined) return null; const d=DL[i]; return (DEFK.has(KINDS[d[1]])?d[7]:Math.min(d[4],d[7]))-(d[6]||d[3])+1; }};
})();
