-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/RunsP.lean: kind K5: the three runs of claims, over the kind's own records
(Att/Geo.lean, Att/Points.lean, Att/TablesP.lean).

Main names:
  `W`: a routine that knows the number of columns of the array of tables, gathers forms in order and
    may refuse.
  `In`: what the runs read. `PadIn`: what the lookup's kind hands in for the test on the padding.
  `firstRun`: the remainder-table units, the softmax-table units and the division: the forms, and the
    calls' key forms as far as they are set.
  `keysRun`: no claim: tests on public numbers on the key forms; it hands the key forms on.
  `secondRun`: the value product; the maximum is attained; the index's cells are bits.
Each routine's text follows the lines of OnBytes/Model (AttentionClaimsA.lean, AttentionClaimsB.lean,
Attention.lean) that its docstring names, with the records exchanged. One place parts from these
lines: "first" begins at as many empty key forms as the place has calls, not at the plan's number. Of OnBytes/Model it calls the
field's arithmetic and the ledger's linear forms.
All its tests are on public numbers.
Not asked here: that a sent word is below the prime (the general fold's).

Definitions with code; no theorem. Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.TablesP

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P.Runs
open OnBytes
open OnBytes.Model (Aff)

instance : Inhabited W1 := ⟨⟨0, 0, zeroE⟩⟩

/-- What the runs read. -/
structure In where
  g : Geo
  p : Pts
  t : TablesP
  /-- each lookup call's key point -/
  zk : Array (Array E)
  /-- the number of the tables' array in the list of arrays -/
  iU3 : Nat

/-- What the lookup's kind hands in for the test on the padding. -/
structure PadIn where
  pub : Array Nat
  noPub : Array Nat
  /-- counts so far · the call · the first place · how many: the counts behind, or a refusal -/
  pubRun : Array Nat → Nat → Nat → Nat → Option (Array Nat)

/-- The calls' key forms, and how often each has been set. After OnBytes/Model/AttentionHeard.lean (Joins). -/
structure JoinsP where
  kf : Array Aff
  joined : Array Nat
def JoinsP.empty (n : Nat) : JoinsP := { kf := Array.replicate n (Aff.ofConst zeroE), joined := Array.replicate n 0 }
def JoinsP.set (j : JoinsP) (q : Nat) (v : Aff) : JoinsP := { kf := j.kf.setIfInBounds q v, joined := j.joined.modify q (· + 1) }

/-- After AttentionHeard.lean:113. -/
def sumW (v : Array W1) : E := v.foldl (fun s x => addE s x.wp) zeroE

/-- After OnBytes/Model/AttentionClaimsA.lean:162-165. -/
def keyKR (pc : RemP) : Aff :=
  let l128 := Aff.ofConst (scaleNat (sumW pc.pw) 128)
  (Aff.slot pc.s0 + l128) + Aff.scale (Aff.slot (pc.s0 + 1) + l128) (ofNat (2 ^ 20)) +
    Aff.scale (Aff.slot (pc.s0 + 2)) (ofNat (2 ^ 40))

/-- After AttentionClaimsA.lean:189-190. -/
def wall (c : CallG) (zk : Array E) : E :=
  c.pcs.foldl (fun s pc => addE s (eqAt (zk.extract 0 (c.n - pc.b)) (pc.off >>> pc.b))) zeroE

/-- After AttentionClaimsA.lean:195-196. -/
def padTerm (c : CallG) (zk : Array E) : Aff := Aff.ofConst (scaleE c.padKey (subE oneE (wall c zk)))

/-- gC · gOm: the two numbers that depend on the call's shift. After AttentionClaimsA.lean:205-214. -/
def keyKFD (gC gOm : Nat) (k : ScoreP) : Aff :=
  let s := k.s0
  let lw := sumW k.pw
  let l128 := Aff.ofConst (scaleNat lw 128)
  let dp := Aff.slot (s + 5) - Aff.slot (s + 6) +
    Aff.ofConst (if k.below then mulE (scaleNat lw gC) (ones k.zs)
      else mulE (scaleNat lw gOm) (subE oneE (leOf k.zj k.zi)))
  dp - (Aff.slot s + l128) - Aff.scale (Aff.slot (s + 1) + l128) (ofNat 256) +
    Aff.scale (Aff.slot (s + 2)) (ofNat (2 ^ 32)) +
    Aff.scale (Aff.slot (s + 3) + l128 + Aff.scale (Aff.slot (s + 4)) (ofNat 256)) (ofNat (2 ^ 33))

/-- After OnBytes/Model/AttentionClaimsB.lean:46, :49. -/
def atRh (S : Geo) : Ten := { off := S.oRh, nl := 1, cnt := S.Lam, J := S.dq }
def atRhp (S : Geo) : Ten := { off := S.oRhp, nl := 1, cnt := S.Lam, J := S.dq }

/-- After AttentionClaimsB.lean:52-53. -/
def remForm (d : DivP) : Aff :=
  Aff.scale (Aff.slot d.sACC) (ofNat 2) + Aff.slot d.sZC - Aff.scale (Aff.slot d.sZO) (ofNat 2)

/-- After AttentionClaimsB.lean:56-58. -/
def indexForm (d : DivP) (lt : Nat) : Aff :=
  (List.range lt).foldl (fun s k => Aff.addMul s (Aff.slot (d.sIB + k)) (ofNat (2 ^ k))) (Aff.ofConst zeroE)

/-- After AttentionClaimsB.lean:62-69. -/
def keyWL (d : DivP) : Aff :=
  let lw := sumW d.pwW
  let l128 := Aff.ofConst (scaleNat lw 128)
  let rem := remForm d
  let tw0 := rem - Aff.scale (Aff.slot d.sRH + l128) (ofNat 65536)
  let tw1 := Aff.scale (Aff.slot d.sZC) (ofNat 2) - Aff.ofConst lw - rem -
    Aff.scale (Aff.slot d.sRHP + l128) (ofNat 65536)
  Aff.scale tw0 (subE oneE d.zsl) + Aff.scale tw1 d.zsl

/-- After AttentionClaimsB.lean:75-77. -/
def keyIX (S : Geo) (d : DivP) : Aff :=
  Aff.scale (Aff.ofConst (mulE (sumW d.pwX) (idOf d.ziX)) - indexForm d S.lt) (ofNat (2 ^ (16 - S.lt)))

/-- After AttentionClaimsB.lean:81-83. -/
def keyWH (d : DivP) : Aff :=
  let l128 := Aff.ofConst (scaleNat (sumW d.pwH) 128)
  (Aff.slot d.s5h + l128) + Aff.scale (Aff.slot (d.s5h + 1) + l128) (ofNat (2 ^ 20))

/-- After AttentionClaimsB.lean:87-96. -/
def joinR16 (S : Geo) (d : DivP) (j : JoinsP) : JoinsP :=
  let tWL := keyWL d
  let tIX := keyIX S d
  S.calls.toList.zipIdx.foldl (fun j x =>
    if x.1.tab == .r16 then
      let v := Aff.ofConst zeroE
      let v := if x.1.holds .wl then v + tWL else v
      let v := if x.1.holds .ix then v + tIX else v
      j.set x.2 v
    else j) j

/-- The units that have a weight in a key form. After OnBytes/Model/Attention.lean:98-102. -/
def weighedUnits (S : Geo) : List (Nat × Keys) :=
  let listed (t : Tab) (ks : List Keys) : List (Nat × Keys) := (S.units t ks).map fun u => (u.1, u.2.2)
  let single (k : Keys) : List (Nat × Keys) := ((S.lastHolding k).map fun q => (q, k)).toList
  listed .kr [.rm, .rd] ++ listed .kfd [.fm, .fd] ++ single .wl ++ single .ix ++ single .wh

/-- After Attention.lean:112-120. -/
def paddingOfCall (k3 : PadIn) (units : List (Nat × Keys)) (q : Nat) (c : CallG) (laid : Array Nat) : Option (Array Nat) := do
  let step (st : Array Nat × Nat) (pc : Pc) : Option (Array Nat × Nat) :=
    if units.contains (q, pc.keys) then pure (st.1, max st.2 (pc.off + 2 ^ pc.b))
    else do
      let l ← k3.pubRun st.1 q pc.off (2 ^ pc.b)
      pure (l, st.2)
  let (l, upto) ← c.pcs.foldlM step (laid, 0)
  k3.pubRun l q upto (2 ^ c.n - upto)

/-- After Attention.lean:123-125. -/
def laidPadding (S : Geo) (k3 : PadIn) : Option (Array Nat) :=
  let units := weighedUnits S
  S.calls.toList.zipIdx.foldlM (fun laid x => paddingOfCall k3 units x.2 x.1 laid) k3.noPub

/-- Knows K; gathers forms in order; may refuse. -/
abbrev W (α : Type) : Type := ReaderT Nat (StateT (Array Aff) Option) α

/-- Appends a form: the claim that it is 0. -/
def W.lin (f : Aff) : W Unit := modify (·.push f)

/-- The value of x, or a refusal. -/
def W.need {α : Type} (x : Option α) : W α := match x with
  | some a => pure a
  | none => failure

/-- A test on public numbers; the name is dropped. -/
def mustAs (_name : String) (b : Bool) : W Unit := if b then pure () else failure

/-- A refusal; the name is dropped. -/
def refuse {α : Type} (_name : String) : W α := failure

/-- The claim that a sumcheck leaves: the stored row. -/
def leftOf (row : Aff) : Aff := row

/-- After OnBytes/Model/Look.lean:58-61. -/
def uEnt (t x : Nat) : W Aff := do
  let cols ← read
  mustAs "internal-L-row" (cols != 0 && x / cols < 2 ^ 32)
  pure (Aff.ent t (x / cols) (x % cols))

/-- After OnBytes/Model/AttentionClaimsA.lean:54-56. -/
def u3at (h : In) (t i : Nat) : W Aff := do
  mustAs "internal-a-table-index" (Decidable.decide (i < (h.t.tabLen.lookup t).getD 0))
  uEnt h.iU3 (t + i)

/-- After OnBytes/Model/AttentionClaimsA.lean:59-62. -/
def weighted (n : Nat) (w : Array E) (f : Nat → W Aff) : W Aff :=
  (List.range n).foldlM (fun s i => do
    let x ← f i
    pure (Aff.addMul s x (w.getD i zeroE))) (Aff.ofConst zeroE)

/-- After OnBytes/Model/AttentionClaimsA.lean:73-79. -/
def plane (h : In) (t x lam a : Nat) (z : Array E) (isD : Bool) : W Aff :=
  let S := h.g
  let nb := if isD then S.nD else S.nM
  let first := (if isD then (5 * S.Lam * S.HA) <<< S.nM else 0) +
    (((x * S.Lam + lam) * S.HA + a) <<< nb)
  let eh := eqTab (z.extract 0 (nb - S.lmS))
  weighted eh.size eh fun hi => u3at h t ((first >>> S.lmS) + hi)

/-- After OnBytes/Model/AttentionClaimsA.lean:84-85. -/
def shV (h : In) (t off nl J lam j : Nat) : W Aff :=
  weighted nl (limbWeights nl) fun l => u3at h t (off + (l * h.g.Lam + lam) * J + j)

/-- After OnBytes/Model/AttentionClaimsA.lean:93-99. -/
def xl (h : In) (t : Nat) (X : Ten) (lam hd : Nat) (zc : Array E) : W Aff := do
  let S := h.g
  let some cut := cutLast (zc.extract 0 S.ldh) S.ls | refuse "plan-tensor-layout"
  let ec := eqTab cut.1
  let some j0 := headFeat X hd S.dh | refuse "plan-tensor-layout"
  weighted ec.size ec fun ch =>
    weighted X.nl (limbWeights X.nl) fun l => u3at h t (tenCell X l lam j0 / 2 ^ S.ls + ch)

/-- After OnBytes/Model/AttentionClaimsA.lean:103-104. -/
def overG (h : In) (zg : Array E) (f : Nat → W Aff) : W Aff :=
  weighted h.g.G (eqTab (zg.extract 0 h.g.lgk)) f

/-- After OnBytes/Model/AttentionClaimsA.lean:108-109. -/
def readDenominator (h : In) (t : Nat) (zg : Array E) (lam a : Nat) : W Aff :=
  overG h zg fun g => shV h t h.g.oZr 4 h.g.H lam (g * h.g.HA + a)

/-- After OnBytes/Model/AttentionClaimsA.lean:113-114. -/
def readMaximum (h : In) (t : Nat) (zg : Array E) (lam a : Nat) : W Aff :=
  overG h zg fun g => shV h t h.g.oMr 4 h.g.H lam (g * h.g.HA + a)

/-- After OnBytes/Model/AttentionClaimsA.lean:119-121. -/
def readIndexBit (h : In) (t : Nat) (zg : Array E) (lam a k : Nat) : W Aff :=
  overG h zg fun g =>
    shV h t h.g.oIb 1 (h.g.lt * h.g.H) lam (k * h.g.H + g * h.g.HA + a)

/-- After OnBytes/Model/AttentionClaimsA.lean:126-127. -/
def readHead (h : In) (t : Nat) (X : Ten) (zg zc : Array E) (lam a : Nat) : W Aff :=
  overG h zg fun g => xl h t X lam (g * h.g.HA + a) zc

/-- After OnBytes/Model/AttentionClaimsA.lean:132-133. -/
def readGroup (h : In) (t : Nat) (X : Ten) (zg zc : Array E) (lam : Nat) : W Aff :=
  overG h zg fun g => xl h t X lam g zc

/-- After OnBytes/Model/AttentionClaimsA.lean:137-140. -/
def lessPieces (start : Aff) (pw : Array W1) (f : W1 → W Aff) : W Aff :=
  pw.foldlM (fun s w => do
    let x ← f w
    pure (Aff.addMul s x (mulE minusOne w.wp))) start

/-- After OnBytes/Model/AttentionClaimsA.lean:144-148. -/
def linPlanes (h : In) (pc : RemP) : W Unit :=
  (List.range pc.np).forM fun x => do
    let f ← lessPieces (Aff.slot (pc.s0 + x)) pc.pw fun w =>
      plane h h.t.tA x w.lam w.a pc.z pc.isD
    W.lin f

/-- After OnBytes/Model/AttentionClaimsA.lean:170-175. -/
def callKR (h : In) (q : Nat) : W Aff :=
  h.p.planes.foldlM (fun v pc =>
    if pc.call == q then do
      linPlanes h pc
      pure (v + keyKR pc)
    else pure v) (Aff.ofConst zeroE)

/-- After OnBytes/Model/AttentionClaimsA.lean:179-184. -/
def claim3 (h : In) (j : JoinsP) : W JoinsP :=
  h.g.calls.toList.zipIdx.foldlM (fun j x =>
    if x.1.tab == .kr then do
      let v ← callKR h x.2
      pure (j.set x.2 v)
    else pure j) j

/-- After OnBytes/Model/AttentionClaimsA.lean:220-225. -/
def endValues (h : In) (k : ScoreP) (tb : ScoreT) (rc : Array E) (b : Nat) (w : W1) :
    W Unit := do
  let q ← readHead h tb.tQ h.g.atQ k.sc.r rc w.lam w.a
  W.lin (k.sc.a b - q)
  let kx ← readGroup h tb.tK h.g.atK k.sc.r rc w.lam
  W.lin (k.sc.b b - kx)

/-- After OnBytes/Model/AttentionClaimsA.lean:231-240. -/
def unitKFD (h : In) (i : Nat) (k : ScoreP) : W Unit := do
  let S := h.g
  let tb ← W.need h.t.score[i]?
  let pc ← W.need h.p.planes[k.claim]?
  linPlanes h pc
  let f ← lessPieces (Aff.slot (k.s0 + 5)) k.pw fun w => readMaximum h tb.tM k.zg w.lam w.a
  W.lin f
  W.lin (leftOf k.sc.row)
  let rc := k.sc.r.extract (k.sc.r.size - S.ldh) k.sc.r.size
  k.pw.toList.zipIdx.forM fun x => endValues h k tb rc x.2 x.1

/-- After OnBytes/Model/AttentionClaimsA.lean:245-251. -/
def callKFD (h : In) (q : Nat) (c : CallG) : W Aff :=
  h.p.scores.toList.zipIdx.foldlM (fun v x =>
    if x.1.call == q then do
      unitKFD h x.2 x.1
      pure (v + keyKFD (h.g.gapC c.sh) (h.g.gapOm c.sh) x.1)
    else pure v) (padTerm c (h.zk.getD q #[]))

/-- After OnBytes/Model/AttentionClaimsA.lean:255-260. -/
def claim4 (h : In) (j : JoinsP) : W JoinsP :=
  h.g.calls.toList.zipIdx.foldlM (fun j x =>
    if x.1.tab == .kfd then do
      let v ← callKFD h x.2 x.1
      pure (j.set x.2 v)
    else pure j) j

/-- After OnBytes/Model/AttentionClaimsB.lean:103-108. -/
def endValuesE (h : In) (b : Nat) (w : W1) : W Unit := do
  let d := h.p.d
  let z ← readDenominator h h.t.hE d.scE.r w.lam w.a
  W.lin (d.scE.a b - z)
  let o ← readHead h h.t.qO h.g.atO d.scE.r d.zcW w.lam w.a
  W.lin (d.scE.b b - o)

/-- After OnBytes/Model/AttentionClaimsB.lean:115-139. -/
def claim5 (h : In) (j : JoinsP) : W JoinsP := do
  let S := h.g
  let d := h.p.d
  let t := h.t
  let zc ← lessPieces (Aff.slot d.sZC) d.pwW fun w => readDenominator h t.hW d.zgW w.lam w.a
  let rh ← lessPieces (Aff.slot d.sRH) d.pwW fun w =>
    readHead h t.tO (atRh S) d.zgW d.zcW w.lam w.a
  let rhp ← lessPieces (Aff.slot d.sRHP) d.pwW fun w =>
    readHead h t.tO (atRhp S) d.zgW d.zcW w.lam w.a
  let r2 ← lessPieces (Aff.slot d.s5h) d.pwH fun w =>
    readHead h t.tO (atRh S) d.zgH d.zcH w.lam w.a
  let r2p ← lessPieces (Aff.slot (d.s5h + 1)) d.pwH fun w =>
    readHead h t.tO (atRhp S) d.zgH d.zcH w.lam w.a
  W.lin zc
  W.lin rh
  W.lin rhp
  for k in List.range S.lt do
    let f ← lessPieces (Aff.slot (d.sIB + k)) d.pwX fun w => readIndexBit h t.hX d.zgX w.lam w.a k
    W.lin f
  W.lin r2
  W.lin r2p
  W.lin (leftOf d.scE.row)
  for b in List.range S.NP do
    endValuesE h b (d.pwW.getD b default)
  pure ((joinR16 S d j).set d.qWH (keyWH d))

/-- After OnBytes/Model/AttentionClaimsB.lean:149-158. -/
def valueProduct (h : In) (sc : SumP) (tS : Nat) (pt : Array E) (isD : Bool) (tV : Nat) :
    W Unit := do
  W.lin (leftOf sc.row)
  for b in List.range h.g.NP do
    let w := h.p.d.pwW.getD b default
    let p3 ← plane h tS 3 w.lam w.a pt isD
    let p4 ← plane h tS 4 w.lam w.a pt isD
    W.lin (sc.a b - (p3 + Aff.ofConst (ofNat 128) + Aff.scale p4 (ofNat 256)))
    let v ← readGroup h tV h.g.atV sc.r h.p.d.zcW w.lam
    W.lin (sc.b b - (Aff.ofConst h.p.d.gam + v))

/-- After OnBytes/Model/AttentionClaimsB.lean:163-168. -/
def claim6 (h : In) : W Unit := do
  let d := h.p.d
  W.lin (Aff.slot d.sCl + Aff.slot (d.sCl + 1) - Aff.slot d.sACC -
    Aff.scale (Aff.slot d.sZC) d.gam)
  valueProduct h d.vpm h.t.tVM h.t.ptM false h.t.qVM
  valueProduct h d.vpd h.t.tVD h.t.ptD true h.t.qVD

/-- After OnBytes/Model/AttentionClaimsB.lean:177-195. -/
def claim7 (h : In) : W Unit := do
  let S := h.g
  let x := h.p.x
  let t := h.t
  for b in List.range S.NP do
    let m ← readMaximum h t.hT x.tg (b / S.HA) (b % S.HA)
    W.lin (Aff.slot (x.sM6 + b) - m)
  W.lin (leftOf x.scF.row)
  for b in List.range S.NP do
    let q ← readHead h t.qF S.atQ (x.rg S) (x.rc S) (b / S.HA) (b % S.HA)
    W.lin (x.scF.a b - q)
  W.lin (leftOf x.scd.row)
  for lam in List.range S.Lam do
    let kx ← readGroup h t.qKx S.atK (x.pg S) (x.rc S) lam
    W.lin (Aff.slot (x.sKC + lam) - kx)
  for b in List.range S.NP do
    for k in List.range S.lt do
      let bit ← readIndexBit h t.hPi (x.pg S) (b / S.HA) (b % S.HA) k
      W.lin (Aff.slot (x.sIb S b k) - bit)

/-- After OnBytes/Model/AttentionClaimsB.lean:203-213. -/
def claim8 (h : In) : W Unit := do
  let S := h.g
  let x := h.p.x
  W.lin (leftOf x.scH.row)
  let ek := eqTab (x.rk S)
  for b in List.range S.NP do
    W.lin (x.scH.b b - x.scH.a b + Aff.ofConst oneE)
    let f ← (List.range S.lt).foldlM (fun s k => do
      let bit ← readIndexBit h h.t.hR2 (x.rg2 S) (b / S.HA) (b % S.HA) k
      pure (Aff.addMul s bit (mulE minusOne (ek.getD k zeroE)))) (x.scH.a b)
    W.lin f

/-- After OnBytes/Model/Attention.lean:105-106. -/
def allJoined (j : JoinsP) : W Unit := do
  mustAs "af-unclosed-call" (j.joined.all (· == 1))

/-- After OnBytes/Model/Attention.lean:134-138; its last line after OnBytes/Model/Look.lean:447-448 (the lookup's one public test, written out). -/
def paddingLaid (S : Geo) (k3 : PadIn) : W Unit := do
  mustAs "internal-af-padding-key"
    (S.calls.all fun c => c.tab == .kfd || c.padKey == 0)
  let some laid := laidPadding S k3 | refuse "internal-forest-pub"
  mustAs "internal-forest-padding-places" (laid == k3.pub)

/-- A routine at K, from no form. -/
def gather {α : Type} (K : Nat) (m : W α) : Option (α × List Aff) :=
  ((m.run K).run #[]).map fun x => (x.1, x.2.toList)

/-- **The run «first».** -/
def firstRun (h : In) (K : Nat) : Option (List Aff × JoinsP) :=
  (gather K (do
    let j ← claim3 h (JoinsP.empty h.g.calls.size)
    let j ← claim4 h j
    claim5 h j)).map fun x => (x.2, x.1)

/-- **The run «keys».** It gathers no form of its own: the key forms are the lookup's join's argument. -/
def keysRun (h : In) (k3 : PadIn) (j : JoinsP) : Option (Array Aff) :=
  (gather 0 (do
    allJoined j
    paddingLaid h.g k3)).map fun _ => j.kf

/-- **The run «second».** -/
def secondRun (h : In) (K : Nat) : Option (List Aff) :=
  (gather K (do
    claim6 h
    claim7 h
    claim8 h)).map (·.2)


end VerifiableInference.Desc.First.Att.P.Runs
