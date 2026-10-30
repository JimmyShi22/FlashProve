-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Goal/HonestTrace/FullInScope.lean

What is known of the trace at the full size ("trFull", Johnson/HonestTrace/Full.lean) for public
files in the goals' scope. This file states no goal.

Johnson/HonestTrace/Full.lean defines the trace: the library's honest cells in the 25 lists of the
sub-proofs, a letter pl in place of the matrices of the lookup's multiplicities, all cut to the
shapes of the verifier's plans. It lies outside Johnson/Goal/ and can call no theorem from there.
The theorems which show that the library's reading functions ("cellsOf", "cellsA", "Hd.cellsH") look
at entries inside the plans' shapes alone, and those which derive the hypotheses on X from the three
premises below, lie under Johnson/Goal/Meaning/. So the laws that need them stand here. "The
verifier" is, in this file, the verifier of OnBytes/Model/ ("OnBytes.Model.Verify").

The three premises. "In scope" means, in the statements below: "VerifierAndGoals.InScope Z = true" (by its
definition in Ladder.lean: the goals' reader accepts the files; the layout file is the stored
full-size example's; the parameter file is that example's but for eight free numbers, the policy's
three among them; 2^8 ≤ theta; the scale file is free), "VerifierAndGoals.readFiles Z = .ok pp" (the goals'
reader returns the settings pp), and "publicOf Z.pol Z.KL lay = .ok X" (the verifier's own function
returns the public part X).

Main theorems; in scope but for the last two, and at every pl unless said otherwise:
* "meetsAll_in_scope": at a request that is served, if pl has the values 0 and 1 alone, the bundle
  "MeetsAll X i x" holds of "trFull X pl i x". Its fields are the theorems that follow.
* "ordsN_in_scope": at a request that is served the trace's lists meet "OrdsN"
  (Johnson/Meaning/Lists.lean). By "ordsL_of_true" (Johnson/Road/Lane5TopLTrue.lean) and three
  theorems that "OrdsN" reads the entries inside the shapes of the matrices that hold cells alone.
* "r0_in_scope", "forIn_layers_in_scope", "forIn_att_in_scope", "forIn_head_in_scope": so each list
  meets its sub-proof's meaning without the lookup clause, and the lookup's clause on keys.
* "borrowed_in_scope": a borrowed matrix has its owner's entries, at all rows and columns, at every
  request, served or not.
* "read_ff_in_scope", "read_att_in_scope", "read_head_in_scope": at every valid name the library's
  reader finds the honest cell in the trace, at every request.
* "zero_off_ff_in_scope", "zero_off_att_in_scope", "zero_off_head_in_scope": an own matrix other
  than the planes' is 0 wherever the library's rule of places puts no valid name's cell, at every
  request.
* "meetsAll_of_traceFull": so every value of "traceFull X pl" meets the bundle, for such pl.
* "cellOf_label_in_scope": the reader by labels, "cellOf", finds the matrix with the name's number.
* "planName_ff_in_scope", "planName_att_in_scope", "planName_head_in_scope": entry number a of the
  verifier's plan of a sub-proof has as its name the label of the name with the number a.
* "packs_in_scope": a guard: at a request that is served, if pl has the values 0 and 1 alone, for
  sizes that follow X's plans with the radix 2^20 and the shift 2^17, the trace can be packed, and
  at synthetic seats the library's reader of packed messages gives it back.
* "no_lists_of_unserved": at a request with r < e that is not served, no lists meet "OrdsN".
* "servesAt_iff_in_scope": "ServesAt X i x" is "true under the policy" at the goals' settings pp.
* "forInG_of_keys_in_scope": at every list, the lookup clause of a group gives the clause "ForInG".
* "parts_in_scope": af, ad, as and hf lie in 3, 1, 1 and 4 parts.
* "cut_eq_cutOf": at every X the cut of Johnson/HonestTrace/Full.lean is the cut to
  "Meaning.sizesAt".
* "premises_met_of_public": a guard; see Limits.

Limits. All is at the reference model's sizes. Every statement in scope is an implication from
"publicOf ... = .ok X". That "publicOf" returns at the stored full-size files is known in this
library by an evaluation ("#guard", Johnson/Goal/Meaning/ScopeRun.lean), not by a theorem that this
file could call: "premises_met_of_public" therefore keeps it as a premise, and shows that the other
premises of "meetsAll_in_scope" on files, index and request are then met together. Its statement
keeps of the request r = 1,023 and e = 1,024, so there is no counted position; in the proof all
tokens and all weights are 0. Which served requests theorems of this library exhibit is said in the
head of Johnson/HonestTrace/Full.lean, "Limits": those named there are all at synthetic weights.
"OrdsN" and the clauses on keys do not read the matrices of multiplicities: what holds "at every pl"
says nothing of pl, not even that it is small. Keys, identities, tables and rules of places are this
library's terms. The key vectors of attention ("kvA") and the places of its cells ("addrA") are
written by a reading of the verifier's texts (Johnson/Road/Lane5BridgeA.lean, Lane5AttDef.lean);
this file ties them to no program. The laws on zeros speak of own matrices: at a borrowed matrix the
entries are the owner's. The shapes are those of the plans' lists; that a run's smallness test goes
by the same lists is not shown here (Johnson/Goal/Meaning/HidPlan.lean, at "follows_sizeOf", says
what is known of it). Johnson/HonestTrace/Places.lean lays cells by formulas of its own, at any
size; no theorem of this file compares its matrices with this trace: FullIsLayInScope.lean in this
folder does, off the planes.

Not claimed: that a prover's committed cells are this trace; that a verifier accepts a proof made of
it (completeness of the protocol); that the claims of any sub-protocol hold at it. The program does
not import this file.

-/
import Johnson.HonestTrace.Full
import Johnson.Goal.Meaning.HidTwelveMet
import Johnson.Goal.Meaning.HidPlanFit
import Johnson.Goal.Meaning.TieR
import Johnson.Goal.Meaning.AttForInScope
import Johnson.Goal.Meaning.HeadForInScope
import Johnson.Goal.Meaning.WeighedScope
import Johnson.Goal.Files.ScopeExample
import Johnson.Road.Lane5KeysIffG
import Johnson.Road.FormsKeysAddr

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.HonestTrace

open Inst.Model Inst.Model.All
open OnBytes.Road OnBytes.Road.L5 OnBytes.Road.Rows.Norms
open OnBytes.Model.Verify (publicOf layerShape borderOf)
open OnBytes.Model.Layer (Lay matIx)
open VerifiableInference.OnPublicFiles.Flat (scalesAt)
open Cb.Pv.Tail (Size)
open Meaning

/-! ## The cut is the cut to the plans' sizes -/

/-- "planMats" (Johnson/HonestTrace/Full.lean) is "Meaning.matsAt"
(Johnson/Goal/Meaning/HidPlan.lean), at every X and number. -/
theorem planMats_eq (X : Model.Verify.Public) (k : ℕ) : planMats X k = matsAt X k := by
  unfold planMats matsAt tlAt
  split_ifs <;> rfl

/-- A place within the sizes "Meaning.sizesAt" lies inside the shape. -/
theorem inShape_of_sizes {X : Model.Verify.Public} {rad beta k a r c : ℕ}
    (h : a < (sizesAt X rad beta k).NM ∧ c < (sizesAt X rad beta k).k a ∧
      r < (sizesAt X rad beta k).m a) :
    InShape X k a r c := by
  unfold InShape
  rw [planMats_eq]
  exact ⟨h.1, h.2.2, h.2.1⟩

/-- **"cut" (Johnson/HonestTrace/Full.lean) is the library's cut to the plans' sizes**: "mzTot" of
"cutOf" at "Meaning.sizesAt", whatever radix and shift stand there. -/
theorem cut_eq_cutOf (X : Model.Verify.Public) (L : Tr) (rad beta k : ℕ) :
    cut X L k = mzTot (cutOf (sizesAt X rad beta k) (L k)) := by
  funext a r c
  by_cases hI : InShape X k a r c
  · rw [cut_in X L hI]
    have hI' := hI
    unfold InShape at hI'
    rw [planMats_eq] at hI'
    exact (mzTot_cutOf (sizesAt X rad beta k) (L k) hI'.1 hI'.2.2 hI'.2.1).symm
  · rw [cut_out X L hI]
    unfold mzTot
    split_ifs with h1 h2 h3
    · exact absurd (inShape_of_sizes ⟨h1, h2, h3⟩) hI
    all_goals rfl

/-! ## Places of names, in the library's matrices and in the lists -/

section Places
variable {hL : Model.Layer.Shape} {pc : List (List String)} {y : Lay}

/-- The place of a valid name in a group's list ("placeOf"), from its place in the library's matrix
of the segment ("Cm.Seg.plFF"): the slot gives the number, the row in the slot the row, the column
the column. If the layers' layout returns y, the shape's switches and sizes are the reference's (S,
Zd, Z2), and the proof covers attention (hp4). -/
theorem placeOf_eq_port (hy : Model.Layer.layout hL pc = .ok y) (S : Switches hL)
    (Zd : Sized hL DF) (Z2 : Sized2 hL DF) (hp4 : hL.p4 = true) (q : FFSeg.Cell)
    (hv : q.Valid DF) :
    placeOf y DF q =
      (portNo y ((Cm.Seg.plFF q).1 / 65536), (Cm.Seg.plFF q).1 % 65536, (Cm.Seg.plFF q).2) := by
  have e : (if (portNo y ((Cm.Seg.plFF q).1 / 65536), (Cm.Seg.plFF q).1 % 65536,
        (Cm.Seg.plFF q).2) = (portNo y ((Cm.Seg.plFF q).1 / 65536), (Cm.Seg.plFF q).1 % 65536,
        (Cm.Seg.plFF q).2) then (1 : ℤ) else 0) =
      if placeOf y DF q = (portNo y ((Cm.Seg.plFF q).1 / 65536), (Cm.Seg.plFF q).1 % 65536,
        (Cm.Seg.plFF q).2) then (1 : ℤ) else 0 :=
    (slot_at y (fun a r c => if (a, r, c) = (portNo y ((Cm.Seg.plFF q).1 / 65536),
      (Cm.Seg.plFF q).1 % 65536, (Cm.Seg.plFF q).2) then (1 : ℤ) else 0) q hv).trans
      (cells_addr_of_layout hy S Zd Z2 _ q hv fun _ => hp4).symm
  rw [if_pos rfl] at e
  by_contra hne
  rw [if_neg hne] at e
  exact one_ne_zero e

/-- If the layers' layout returns y and the shape's switches and sizes are the reference's (S, Zd,
Z2), a matrix of a group's list that holds cells (any but b) has at most 65,536 rows. -/
theorem rowsM_le (hy : Model.Layer.layout hL pc = .ok y) (S : Switches hL) (Zd : Sized hL DF)
    (Z2 : Sized2 hL DF) {μ : FFSeg.Mx} (hμ : μ ≠ .b) : rowsM y (mxNo μ) ≤ 65536 := by
  have e := (admitted_of_layout hy S.p3).shape
  subst e
  rw [rowsM_eq (laid2_of_layout hy) Zd Z2 hμ]
  cases μ <;> first | exact absurd rfl hμ | decide

/-- Where "as" lies in one part, the list that is read out of the library's matrices has at its
three own numbers the three slots of the attention segment's matrix. -/
theorem zsOf_own1 {S : Attention.Shape} (n1 : S.cf.NAs = 1) (g : ℕ) (M : Mx) {a : ℕ} (ha : a < 3)
    (r c : ℕ) : zsOf S g M a r c = M (2 * g + 1) (a * 65536 + r) c := by
  have c3 : a = 0 ∨ a = 1 ∨ a = 2 := by omega
  rcases c3 with rfl | rfl | rfl
  · rw [zsOf_as S g M (by omega) r c]
    simp only [Nat.zero_mul, Nat.zero_add]
  · have e := zsOf_ah S g M r c
    rw [n1] at e
    exact e
  · have e := zsOf_ao S g M r c
    rw [n1] at e
    exact e

end Places

/-! ## The names in the plans of the layer sub-proofs -/

section PlanNames
open OnBytes.Model (TMat T2Foreign Settings)
open OnBytes.Model.Layer (Pub HPlan2 Scales bordersOf planG plansFrom plansG tailsOf)

/-- "bordersOf" keeps the matrices' order, number and names. -/
theorem bordersOf_names {y : Lay} {ms : Array TMat}
    {r : Array TMat × Array (Option ℕ) × Array T2Foreign} (h : bordersOf y ms = .ok r) :
    (r.1.map fun M => M.name) = ms.map fun M => M.name := by
  unfold bordersOf at h
  obtain ⟨-, h⟩ := ok_of_refuse h
  have e := (Except.ok.inj h).symm
  subst e
  have H : ∀ (l : List (TMat × ℕ))
      (s : Array TMat × Array (Option ℕ) × Array T2Foreign × ℕ),
      ((l.foldl (fun (s : Array TMat × Array (Option ℕ) × Array T2Foreign × ℕ) x =>
        if (x.1.kind == 0 && (x.2 == (Model.Layer.matIx y).iXO ||
            (y.h.p4 && x.2 == (Model.Layer.matIx y).iQA))) = true then
          (s.1.push x.1, s.2.1.push (some s.2.2.2), s.2.2.1, s.2.2.2 + 1)
        else if (x.1.kind == 1) = true then
          (s.1.push { x.1 with foreign := some s.2.2.1.size, ttOff := 0 }, s.2.1.push none,
           s.2.2.1.push { name := "PXf" ++ toString s.2.2.1.size, K := x.1.k, a := 2, m := x.1.m,
                          wp := x.1.wp }, s.2.2.2)
        else (s.1.push x.1, s.2.1.push none, s.2.2.1, s.2.2.2)) s).1.toList.map
          fun M => M.name) =
        (s.1.toList.map fun M => M.name) ++ l.map fun x => x.1.name := by
    intro l
    induction l with
    | nil =>
      intro s
      simp
    | cons x l ih =>
      intro s
      rw [List.foldl_cons, ih]
      split_ifs <;> simp
  have h1 := H ms.toList.zipIdx (#[], #[], #[], 0)
  apply Array.ext'
  rw [Array.toList_map, Array.toList_map]
  refine Eq.trans h1 ?_
  have h2 : (ms.toList.zipIdx.map fun x => x.1.name) =
      (ms.toList.zipIdx.map (·.1)).map fun M => M.name := by
    rw [List.map_map]
    rfl
  rw [h2, List.zipIdx_map_fst]
  simp

/-- In the plans that "plansG" returns for the public numbers of the layout y, the list of matrices
in the plan of group g has the names of the list of "tailsOf", in order. -/
theorem plan_names {y : Lay} {sc : Scales} {rope : Array ℕ} {wsLay : Model.WsLay} {V : ℕ}
    {tokv : Array ℕ} {set : Settings} {P : Pub} (hP : Pub.of y sc rope wsLay V tokv set = .ok P)
    {G : Array HPlan2} (hG : plansG P = .ok G) (g : ℕ) (hp : HPlan2) (hg : G[g]? = some hp) :
    (hp.tl.mats.map fun M => M.name) = ((tailsOf y).getD g {}).mats.map fun M => M.name := by
  unfold Pub.of at hP
  obtain ⟨-, hP⟩ := ok_of_refuse hP
  obtain ⟨rd, -, hP⟩ := ok_of_bind hP
  have e := (Except.ok.inj hP).symm
  subst e
  unfold plansG at hG
  obtain ⟨l, hl, hG⟩ := ok_of_bind hG
  have e := (Except.ok.inj hG).symm
  subst e
  have hg' : l[g]? = some hp := by simpa using hg
  obtain ⟨O', hO⟩ := plansFrom_at _ _ 0 none l hl g hp hg'
  rw [Nat.zero_add] at hO
  obtain ⟨b, hb, e⟩ := Hd.planG_mats hO
  rw [e]
  exact bordersOf_names hb

/-- For g below the layout's number of groups, the names of the matrices of group g in the list of
"tailsOf" are the names in "asksTab". -/
theorem tails_names (y : Lay) {g : ℕ} (hg : g < y.NGr) :
    (((tailsOf y).getD g {}).mats.map fun M => M.name) = ((asksTab y).map (·.1)).toArray := by
  rw [tailsOf_eq, getD_range_map _ _ _ _ hg]
  show (((asksTab y).zipIdx.map (tmatTab y g)).toArray.map fun M => M.name) = _
  rw [List.map_toArray, List.map_map]
  have e : ((fun M : TMat => M.name) ∘ tmatTab y g) =
      ((·.1) : String × ℕ × ℕ → String) ∘ Prod.fst := funext fun x => by
    show (tmatTab y g x).name = x.1.1
    unfold tmatTab
    dsimp only
    split <;> rfl
  rw [e, ← List.map_map, List.zipIdx_map_fst]

end PlanNames

section Core
variable {pol KL : ByteArray} {lay : Option ByteArray} {X : Model.Verify.Public}

/-- If "publicOf" returns X and the 41 numbers of X's parameter file are the reference's and
its lines gcl and rcl are there ("Hd.PublicCore"): in the plan of group g, g < 12, the entry of part
p of the matrix with the number mat (af, ad, ar, qa, xbI, xbO) has the rows "rowsM" and the columns
"colsM" of the layers' layout.
-/
theorem entry_eq (h : publicOf pol KL lay = .ok X) (C : Hd.PublicCore X.P) {g : ℕ} (hg : g < 12)
    {mat p : ℕ} (hmat : mat ≤ 5) (hp : p < partsM X.y mat) :
    ((matsAt X (2 * g)).getD (firstM X.y mat + p) {}).m = rowsM X.y mat ∧
      ((matsAt X (2 * g)).getD (firstM X.y mat + p) {}).k = colsM X.y mat := by
  have B := (Hd.eleven_of_core h C (Hd.npOf X.hS)).1
  obtain ⟨sc, rope, wsLay, V, tokv, set, hP, hG⟩ := Hd.public_plans h
  obtain ⟨P, e⟩ := planG_there h C hg
  obtain ⟨l1, l2⟩ := sizesTab_at X.y hmat hp
  have k0 := congrArg (fun z : Array (ℕ × ℕ) => z[firstM X.y mat + p]?) (plan_sizes hP hG e).1
  have k : (P.tl.mats[firstM X.y mat + p]?).map (fun M => (M.m, M.k)) =
      some (rowsM X.y mat, colsM X.y mat) := by
    have k1 : (P.tl.mats[firstM X.y mat + p]?).map (fun M => (M.m, M.k)) =
        (matsR X.y g)[firstM X.y mat + p]? := by simpa using k0
    rw [k1]
    unfold matsR
    rw [tails_pairs X.y (by rw [B.groups]; exact hg), List.getElem?_toArray, ← l2,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem l1]
    rfl
  rw [matsAt_even hg e]
  cases hM : P.tl.mats[firstM X.y mat + p]? with
  | none =>
    rw [hM] at k
    cases k
  | some M =>
    rw [hM] at k
    have k2 : (M.m, M.k) = (rowsM X.y mat, colsM X.y mat) := Option.some.inj k
    rw [getD_of hM]
    exact ⟨congrArg Prod.fst k2, congrArg Prod.snd k2⟩

/-- If "publicOf" returns X and the 41 numbers of X's parameter file are the reference's and
its lines gcl and rcl are there ("Hd.PublicCore"): none of the eight matrices that fill a slot of
the library's matrix of a group has the number of b. -/
theorem portNo_ne_planes (h : publicOf pol KL lay = .ok X) (C : Hd.PublicCore X.P) {σ : ℕ}
    (hσ : σ < 8) : portNo X.y σ ≠ (matIx X.y).iB := by
  have B := (Hd.eleven_of_core h C (Hd.npOf X.hS)).1
  obtain ⟨p0, p1⟩ := Hd.parts_ref B.lay B.switches B.sized2
  have e : (matIx X.y).iB = X.y.parts.getD 0 0 + X.y.parts.getD 1 0 + 1 := rfl
  rw [e, p0, p1]
  interval_cases σ <;> simp only [portNo, firstM, matIx, p0, p1] <;> omega

/-- If "publicOf" returns X and the 41 numbers of X's parameter file are the reference's and
its lines gcl and rcl are there ("Hd.PublicCore"): for g < 12 no valid name of an attention segment
has its place, by the rule "addrA", in the matrix bA. -/
theorem addrA_ne_planes (h : publicOf pol KL lay = .ok X) (C : Hd.PublicCore X.P) {g : ℕ}
    (hg : g < 12) (c : AttSeg.Raw) (hv : c.Valid (dimOf (Hd.shapeA X g))) :
    (addrA (Hd.shapeA X g) c).1 ≠ (Hd.shapeA X g).cf.NAs + 2 := by
  intro e
  have P := planSizes_of_follows h C (follows_sizesAt X 0 0) hg
  have P' : PlanSizes { sizesAt X 0 0 (2 * g + 1) with
      k := fun a => if a = (Hd.shapeA X g).cf.NAs + 2 then 0
        else (sizesAt X 0 0 (2 * g + 1)).k a } (Hd.shapeA X g) :=
    ⟨P.NM, P.asM, fun q hq => (if_neg (by omega)).trans (P.asK q hq), P.ahM,
      (if_neg (by omega)).trans P.ahK, P.aoM, (if_neg (by omega)).trans P.aoK, P.qaM,
      (if_neg (by omega)).trans P.qaK⟩
  have I := (inside_of_core h C hg P' c hv).2.1
  rw [e] at I
  exact absurd (lt_of_lt_of_eq I (if_pos rfl)) (Nat.not_lt_zero _)

/-- Two entries of the plans' lists that pass the test "pairFit" (both are there, with one label and
the same rows and columns), neither the planes': if the lists without planes and without the cut
agree there at all rows and columns, so does the trace. -/
theorem trFull_pair (X : Model.Verify.Public) (pl : ℕ → ℕ → ℕ → ℤ) (i : Cm.Idx)
    (x : Instance ppref) {k a k' a' : ℕ} (p : pairFit X k a k' a' = true) (ha : a ≠ bNo X k)
    (ha' : a' ≠ bNo X k')
    (e : ∀ r c, listsOf X (honMx X i x) k a r c = listsOf X (honMx X i x) k' a' r c) (r c : ℕ) :
    trFull X pl i x k a r c = trFull X pl i x k' a' r c := by
  unfold pairFit at p
  simp only [Bool.and_eq_true, decide_eq_true_eq] at p
  obtain ⟨⟨⟨⟨s1, s2⟩, em⟩, ek⟩, -⟩ := p
  have hI : InShape X k a r c ↔ InShape X k' a' r c := by
    unfold InShape
    rw [planMats_eq, planMats_eq, em, ek]
    exact ⟨fun H => ⟨s2, H.2⟩, fun H => ⟨s1, H.2⟩⟩
  by_cases H : InShape X k a r c
  · rw [trFull_cells X pl i x H ha, trFull_cells X pl i x (hI.1 H) ha', e]
  · rw [trFull_out X pl i x H, trFull_out X pl i x fun H' => H (hI.2 H')]

/-- If "publicOf" returns X and the 41 numbers of X's parameter file are the reference's and
its lines gcl and rcl are there ("Hd.PublicCore"): **a borrowed matrix has its owner's entries**, at
all rows and columns, at every pl, index and request: the stream that enters a later group is the
stream that left the group before; an attention sub-proof's qa is its group's; the head's stream is
the stream that left group 11. -/
theorem borrowed_core (h : publicOf pol KL lay = .ok X) (C : Hd.PublicCore X.P)
    (pl : ℕ → ℕ → ℕ → ℤ) (i : Cm.Idx) (x : Instance ppref) :
    (∀ g, 0 < g → g < 12 → ∀ r c, trFull X pl i x (2 * g) (matIx X.y).iXI r c =
      trFull X pl i x (2 * (g - 1)) (matIx X.y).iXO r c) ∧
    (∀ g < 12, ∀ r c, trFull X pl i x (2 * g + 1) ((Hd.shapeA X g).cf.NAs + 3) r c =
      trFull X pl i x (2 * g) (matIx X.y).iQA r c) ∧
    ∀ r c, trFull X pl i x 24 (X.hS.NHf + 3) r c = trFull X pl i x 22 (matIx X.y).iXO r c := by
  have B := (Hd.eleven_of_core h C (Hd.npOf X.hS)).1
  obtain ⟨p0, p1⟩ := Hd.parts_ref B.lay B.switches B.sized2
  obtain ⟨q1, q2, q3⟩ := pairs_of_planFit (planFit_of_core h C)
  obtain ⟨l1, l2, l3⟩ := listsOf_eq_true X i x
  have nI : (matIx X.y).iXI ≠ (matIx X.y).iB := by
    show X.y.parts.getD 0 0 + X.y.parts.getD 1 0 + 4 ≠ X.y.parts.getD 0 0 + X.y.parts.getD 1 0 + 1
    omega
  have nO : (matIx X.y).iXO ≠ (matIx X.y).iB := by
    show X.y.parts.getD 0 0 + X.y.parts.getD 1 0 + 3 ≠ X.y.parts.getD 0 0 + X.y.parts.getD 1 0 + 1
    omega
  have nQ : (matIx X.y).iQA ≠ (matIx X.y).iB := by
    show X.y.parts.getD 0 0 + X.y.parts.getD 1 0 + 2 ≠ X.y.parts.getD 0 0 + X.y.parts.getD 1 0 + 1
    omega
  refine ⟨fun g h0 hg => trFull_pair X pl i x (q1 g h0 hg) (by rw [bNo_even X hg]; exact nI)
      (by rw [bNo_even X (by omega)]; exact nO) fun r c => ?_,
    fun g hg => trFull_pair X pl i x (q2 g hg) (by rw [bNo_odd]; omega)
      (by rw [bNo_even X hg]; exact nQ) fun r c => ?_,
    trFull_pair X pl i x q3 (by rw [bNo_head]; omega)
      (by rw [show (22 : ℕ) = 2 * 11 from rfl, bNo_even X (by norm_num)]; exact nO) fun r c => ?_⟩
  · rw [l1 g hg, l1 (g - 1) (by omega)]
    show Hd.zOf (honMx X i x) (labA X.y g (matIx X.y).iXI) r c =
      Hd.zOf (honMx X i x) (labA X.y (g - 1) (matIx X.y).iXO) r c
    rw [Hd.labA_in X.y h0]
  · rw [l2 g, l1 g hg]
    exact (zsOf_qa _ g _ r c).trans (Hd.zOf_qa p0 p1 _ hg r c).symm
  · rw [l3, show (22 : ℕ) = 2 * 11 from rfl, l1 11 (by norm_num)]
    show Hd.zOf (honMx X i x) (Hd.labH X.hS X.y (X.hS.NHf + 3)) r c =
      Hd.zOf (honMx X i x) (labA X.y 11 (matIx X.y).iXO) r c
    unfold Hd.labH
    rw [if_pos rfl, B.groups]

/-- If "publicOf" returns X and the 41 numbers of X's parameter file are the reference's and
its lines gcl and rcl are there ("Hd.PublicCore"): within the four ranges of "Hd.SmallH" (the parts
of hf, hd, hr, the borrowed stream, inside their shapes) the trace's list of the head is the list
without planes and without the cut. -/
theorem agreeH_core (h : publicOf pol KL lay = .ok X) (C : Hd.PublicCore X.P)
    (pl : ℕ → ℕ → ℕ → ℤ) (i : Cm.Idx) (x : Instance ppref) :
    AgreeH X.hS X.HLy (borderOf X.y) (Hd.mzH X.hS X.y (Hd.zOf (honMx X i x)))
      (trFull X pl i x 24) := by
  obtain ⟨q1, q2, q3, q4⟩ := head_in h C (follows_sizesAt X 0 0)
  have l3 := (listsOf_eq_true X i x).2.2
  refine ⟨fun a ha r hr' c hc' => ?_, fun r hr' c hc' => ?_, fun r hr' c hc' => ?_,
    fun r hr' c hc' => ?_⟩
  · obtain ⟨a1, a2, a3⟩ := q1 a ha
    rw [trFull_cells X pl i x (inShape_of_sizes ⟨a1, a3 ▸ hc', a2 ▸ hr'⟩)
      (by rw [bNo_head]; omega), l3]
    rfl
  · obtain ⟨a1, a2, a3⟩ := q2
    rw [trFull_cells X pl i x (inShape_of_sizes ⟨a1, a3 ▸ hc', a2 ▸ hr'⟩)
      (by rw [bNo_head]; omega), l3]
    rfl
  · obtain ⟨a1, a2, a3⟩ := q3
    rw [trFull_cells X pl i x (inShape_of_sizes ⟨a1, a3 ▸ hc', a2 ▸ hr'⟩)
      (by rw [bNo_head]; omega), l3]
    rfl
  · obtain ⟨a1, a2, a3⟩ := q4
    rw [trFull_cells X pl i x (inShape_of_sizes ⟨a1, a3 ▸ hc', a2 ▸ hr'⟩)
      (by rw [bNo_head]; omega), l3]
    rfl

/-- If "publicOf" returns X and the 41 numbers of X's parameter file are the reference's and
its lines gcl and rcl are there ("Hd.PublicCore"), X's table of scales is lawful, its policy is
within the library's bounds, and the request is served: the trace's lists meet "OrdsN", whatever pl
is. "OrdsN" does not read the matrices of multiplicities. -/
theorem ordsN_core (h : publicOf pol KL lay = .ok X) (C : Hd.PublicCore X.P)
    (hs : (scalesAt X).Lawful) (hpol : Policy.PolCond (Hd.polOf X.hS)) (pl : ℕ → ℕ → ℕ → ℤ)
    {i : Cm.Idx} {x : Instance ppref} (T : ServesAt X i x) :
    OrdsN (layerShape X.P) X.layers.sc X.y X.hS X.HLy (Hd.npOf X.hS) (Hd.polOf X.hS)
      (Hd.shapeA X) i.mat x (fun g => trFull X pl i x (2 * g))
      (fun g => trFull X pl i x (2 * g + 1)) (trFull X pl i x 24) := by
  have E := Hd.eleven_of_core h C (Hd.npOf X.hS)
  have B := E.1
  have F := follows_sizesAt X 0 0
  have N := lists_of_ordsL B.groups
    (ordsL_of_true B.lay B.switches B.sized B.sized2 B.p4 B.groups B.full B.head E.2.1
      E.2.2.2.2 E.2.2.1 E.2.2.2.1 hs hpol i x T)
  obtain ⟨l1, l2, l3⟩ := listsOf_eq_true X i x
  obtain ⟨b1, b2, b3⟩ := borrowed_core h C pl i x
  refine ⟨fun g hg => ?_, fun g hg => ?_, ?_, b1, b2, b3⟩
  · refine layerOrd_congr_core h C hg (fun σ r c hz => ?_) (N.layer g hg)
    rw [trFull_cells X pl i x (inShape_of_sizes (inZ_in h C F hg hz))
      (by rw [bNo_even X hg]; exact portNo_ne_planes h C hz.1), l1 g hg]
    rfl
  · refine ord_of_ownA ((ownA_congr fun c hv => ?_).mp (ownA_of_ord (N.att g hg)))
    unfold zAt
    rw [trFull_cells X pl i x (inShape_of_sizes (inside_of_follows h C F hg c hv))
      (by rw [bNo_odd]; exact addrA_ne_planes h C hg c hv), l2 g]
    rfl
  · exact headOrd_congr (Hd.numH_of_layout B.full B.head)
      (Hd.borderH_of_layout B.lay B.switches B.sized B.sized2) (agreeH_core h C pl i x) N.head

end Core

/-! ## In scope -/

section Scope
variable {Z : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : Option ByteArray} {X : Model.Verify.Public}

/-- Under the three premises on the public files (Z is in the goals' scope; the goals' reader
returns pp; "publicOf" returns X): "ServesAt X i x" is "true under the policy" at the scales and the
policy of the goals' settings pp. -/
theorem servesAt_iff_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) (i : Cm.Idx) (x : Instance ppref) :
    ServesAt X i x ↔ Policy.IsTrueUnder (Cm.Scales.of pp) pp.pol i x := by
  have A := Hd.core_of_scope hZ hR h
  obtain ⟨tP, tS⟩ := VerifiableInference.Meaning.readings_agree Z pp lay X hR h
  have tS' : Cm.Scales.of pp = scalesAt X := tS (A.num 2)
  rw [tS', tP]
  exact Iff.rfl

/-- Under the three premises on the public files (Z is in the goals' scope; the goals' reader
returns pp; "publicOf" returns X): X's table of scales is lawful and its policy is within the
library's bounds. -/
theorem lawful_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) :
    (scalesAt X).Lawful ∧ Policy.PolCond (Hd.polOf X.hS) := by
  have A := Hd.core_of_scope hZ hR h
  obtain ⟨tP, tS⟩ := VerifiableInference.Meaning.readings_agree Z pp lay X hR h
  have tS' : Cm.Scales.of pp = scalesAt X := tS (A.num 2)
  exact ⟨tS' ▸ lawful_of_read hR, tP ▸ polCond_of_read hR⟩

/-- Under the three premises on the public files (Z is in the goals' scope; the goals' reader
returns pp; "publicOf" returns X), at a request that is served: every entry of the trace off the
planes' number is below 129 in absolute value, at all numbers, rows and columns, whatever pl is. Of
the planes nothing is said. -/
theorem small_off_planes_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) (pl : ℕ → ℕ → ℕ → ℤ) {i : Cm.Idx}
    {x : Instance ppref} (T : ServesAt X i x) (k a r c : ℕ) (ha : a ≠ bNo X k) :
    |trFull X pl i x k a r c| < 129 :=
  trFull_small (lawful_in_scope hZ hR h).1 (lawful_in_scope hZ hR h).2 pl T k a r c ha

/-- Under the three premises on the public files (Z is in the goals' scope; the goals' reader
returns pp; "publicOf" returns X): **a borrowed matrix has its owner's entries**, at all rows and
columns, at every pl, index and request, served or not: the stream that enters a later group is the
stream that left the group before; an attention sub-proof's qa is its group's; the head's stream is
the stream that left group 11. -/
theorem borrowed_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) (pl : ℕ → ℕ → ℕ → ℤ) (i : Cm.Idx)
    (x : Instance ppref) :
    (∀ g, 0 < g → g < 12 → ∀ r c, trFull X pl i x (2 * g) (matIx X.y).iXI r c =
      trFull X pl i x (2 * (g - 1)) (matIx X.y).iXO r c) ∧
    (∀ g < 12, ∀ r c, trFull X pl i x (2 * g + 1) ((Hd.shapeA X g).cf.NAs + 3) r c =
      trFull X pl i x (2 * g) (matIx X.y).iQA r c) ∧
    ∀ r c, trFull X pl i x 24 (X.hS.NHf + 3) r c = trFull X pl i x 22 (matIx X.y).iXO r c :=
  borrowed_core h (Hd.core_of_scope hZ hR h) pl i x

/-- **The trace meets "OrdsN".** Under the three premises on the public files (Z is in the goals'
scope; the goals' reader returns pp; "publicOf" returns X), at a request that is served, whatever pl
is: in each group's list and in the head's the entries inside the shapes of the matrices that hold
cells, and in each attention list the cells at valid names, are below 2^18 in absolute value; every
identity of the library is 0 modulo the prime; every entry of the library's key vectors is in the
library's table; and every borrowed matrix has its owner's entries. Of b, bA and bH nothing is said,
not even that they are small. -/
theorem ordsN_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) (pl : ℕ → ℕ → ℕ → ℤ) {i : Cm.Idx}
    {x : Instance ppref} (T : ServesAt X i x) :
    OrdsN (layerShape X.P) X.layers.sc X.y X.hS X.HLy (Hd.npOf X.hS) (Hd.polOf X.hS)
      (Hd.shapeA X) i.mat x (fun g => trFull X pl i x (2 * g))
      (fun g => trFull X pl i x (2 * g + 1)) (trFull X pl i x 24) :=
  ordsN_core h (Hd.core_of_scope hZ hR h) (lawful_in_scope hZ hR h).1
    (lawful_in_scope hZ hR h).2 pl T

/-- Under the three premises on the public files (Z is in the goals' scope; the goals' reader
returns pp; "publicOf" returns X), at a request that is served, whatever pl is: each group's list
meets "LayerR0", each attention list "AttR0" and the head's list "HeadR0": the meaning of the
sub-proof without its lookup clause (of the matrices that hold cells: small; every identity of the
library 0 modulo the prime).
-/
theorem r0_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) (pl : ℕ → ℕ → ℕ → ℤ) {i : Cm.Idx}
    {x : Instance ppref} (T : ServesAt X i x) :
    (∀ g < 12, LayerR0 (layerShape X.P) X.layers.sc X.y g (trFull X pl i x (2 * g)) i.mat x) ∧
    (∀ g < 12, AttR0 (Hd.shapeA X g) (trFull X pl i x (2 * g + 1))) ∧
    HeadR0 X.hS X.HLy X.y (Hd.npOf X.hS) (Hd.polOf X.hS) x (trFull X pl i x 24) :=
  have O := ordsN_in_scope hZ hR h pl T
  ⟨fun g hg => (layerOrd_iff_split.1 (O.layer g hg)).1,
    fun g hg => (attOrd_iff_split.1 (O.att g hg)).1, (headOrdLB_iff_split.1 O.head).1⟩

/-- Under the three premises on the public files (Z is in the goals' scope; the goals' reader
returns pp; "publicOf" returns X), at a request that is served, g < 12, whatever pl is: every entry
of the library's key vectors "kvA" at the trace's attention list is a row of the table that the
lookup shape of the group's plan gives the call: as the clause "ForInA", and as "InTables" at
"callsA". -/
theorem forIn_att_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) (pl : ℕ → ℕ → ℕ → ℤ) {i : Cm.Idx}
    {x : Instance ppref} (T : ServesAt X i x) {g : ℕ} (hg : g < 12) :
    ForInA (Hd.shapeA X g) (Meaning.Att.fsA X g) (cellZ (trFull X pl i x (2 * g + 1))) ∧
    (callsA (Hd.shapeA X g) (Meaning.Att.fsA X g) (trFull X pl i x (2 * g + 1))).InTables :=
  have I := ((Meaning.Att.attOrd_iff_forIn_in_scope hZ hR h hg _).1
    ((ordsN_in_scope hZ hR h pl T).att g hg)).2
  ⟨I, (Meaning.Att.forInA_iff_in_scope hZ hR h hg _).1 I⟩

/-- Under the three premises on the public files (Z is in the goals' scope; the goals' reader
returns pp; "publicOf" returns X), at a request that is served, whatever pl is, and a value R of the
head's run data that has X's shape and layout and fits the request ("Hd.ReqFits"; "Hd.runReq R0 x"
is such a value for every R0 with that shape and layout: Johnson/Road/Ends/HeadWit.lean): the clause
"Hd.ForInH" holds of the head's key vectors at the trace's list of the head and the index's matrix
of the weights' digits (i.mat).
-/
theorem forIn_head_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) (pl : ℕ → ℕ → ℕ → ℤ) {i : Cm.Idx}
    {x : Instance ppref} (T : ServesAt X i x) {R : Model.Head.Run} (e1 : R.h = X.hS)
    (e2 : R.L = X.HLy) (Rq : Hd.ReqFits R HeadSizes.ref (Head.Req.of (Hd.polOf X.hS) x)) :
    Hd.ForInH R (Hd.callsH R (borderOf X.y) X.layers.wsLay (trFull X pl i x 24) i.mat).K :=
  ((Meaning.HeadS.headOrd_iff_in_scope hZ hR h e1 e2 Rq i.mat _).1
    (ordsN_in_scope hZ hR h pl T).head).2

section Back
open Meaning.P34 OnBytes.Model OnBytes.Ends

/-- Under the three premises on the public files (Z is in the goals' scope; the goals' reader
returns pp; "publicOf" returns X), g < 12, at every list Mz, matrix Wi and array of tokens: the
lookup clause of the group ("LayerKeys") gives the clause "Alg.ForInG". The other direction is
"Meaning.P34.layerKeys_of_scope" (Johnson/Goal/Meaning/WeighedScope.lean). By "Alg.forInG_iff_keys",
with its public hypotheses proved as there. -/
theorem forInG_of_keys_in_scope (hZ : VerifierAndGoals.InScope Z = true)
    (hR : VerifierAndGoals.readFiles Z = .ok pp) (h : publicOf Z.pol Z.KL lay = .ok X) (tokv : Array ℕ)
    {g : ℕ} (hg : g < 12) {Mz : Mats ℤ} {Wi : Mat}
    (K : LayerKeys (layerShape X.P) X.layers.sc X.y g Mz Wi) :
    Alg.ForInG (Meaning.P34.pubAt X tokv) g Mz Wi := by
  obtain ⟨mats, r, hl⟩ := hl_in_scope hZ hR h g
  obtain ⟨hy, S, hs, hrd, Zd, -, hN, hfl, Zw, -, hlw, h4⟩ := pub34_public hZ hR h
  have A := Hd.core_of_scope hZ hR h
  have B := Hd.public_of_core h A
  have hsh := shape_in_scope hZ hR h
  have hLam : X.y.Lam = 4 := by
    rw [(laid_of_layout hy S.p3).2.Lam, shape_of_public h, hsh]
    rfl
  have h8 : X.y.calls.size = 8 := by
    have := congrArg List.length hN
    simpa using this
  exact (Alg.forInG_iff_keys (P := pubAt X tokv) (rd := X.layers.rd) hy S hs
    (by show g < X.y.NGr; rw [B.groups]; exact hg) hrd hl Zd h4
    (by rw [show (layerShape X.P).dh = 128 from A.num 7]) (hmats_of_layout hy S.p3)
    (by
      show X.y.T = DF.T
      rw [(laid2_of_layout hy).T, shape_of_public h, hsh]
      rfl)
    Zw hlw
    (fun l hl4 => by
      show g * X.y.Lam + l < 48
      have : l < 4 := hl4
      rw [hLam]
      omega)
    (Rope.ropeOK_in_scope hZ hR h hg) h8
    (fun cc cd hcd => by
      have e := line_at hN cc
      have eg : X.y.calls.getD cc.val default = cd := by
        have hq : cc.val < X.y.calls.size := by rw [h8]; exact cc.isLt
        have hcd' : X.y.calls[cc.val]? = some cd := hcd
        rw [Array.getElem?_eq_getElem hq] at hcd'
        simp [Array.getD, hq, Option.some.inj hcd']
      rw [eg] at e
      exact e)
    hfl (fun cd hcd => weighed_in_scope hZ hR h cd hcd) (hL_in_scope hZ hR h) Mz Wi).2 K

end Back

/-- Under the three premises on the public files (Z is in the goals' scope; the goals' reader
returns pp; "publicOf" returns X), at a request that is served, g < 12, whatever pl and the array of
tokens are: the clause "Alg.ForInG" holds at the trace's list of group g and the index's matrix of
the weights' digits (i.mat): every entry of the library's key vectors "kvG" is a row of its call's
table. -/
theorem forIn_layers_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) (pl : ℕ → ℕ → ℕ → ℤ) {i : Cm.Idx}
    {x : Instance ppref} (T : ServesAt X i x) (tokv : Array ℕ) {g : ℕ} (hg : g < 12) :
    Alg.ForInG (Meaning.P34.pubAt X tokv) g (trFull X pl i x (2 * g)) i.mat :=
  forInG_of_keys_in_scope hZ hR h tokv hg
    (layerOrd_iff_split.1 ((ordsN_in_scope hZ hR h pl T).layer g hg)).2

/-- Under the three premises on the public files (Z is in the goals' scope; the goals' reader
returns pp; "publicOf" returns X), g < 12, at every pl, index and request, served or not: at every
valid name of a feed-forward segment the reader inside "LayerOrd" ("cellsOf" of "cellsAt") finds in
the trace's list of group g the cell that the honest cells' reading "vFF g" has there. For the
stream that enters a later group that is a cell of the group before. -/
theorem read_ff_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) (pl : ℕ → ℕ → ℕ → ℤ) (i : Cm.Idx)
    (x : Instance ppref) {g : ℕ} (hg : g < 12) (c : FFSeg.Cell) (hc : c.Valid DF) :
    cellsOf DF (cellsAt X.y (trFull X pl i x (2 * g))) c = (honAt X i x).vFF g c := by
  have C := Hd.core_of_scope hZ hR h
  have B := (Hd.eleven_of_core h C (Hd.npOf X.hS)).1
  obtain ⟨p0, p1⟩ := Hd.parts_ref B.lay B.switches B.sized2
  have H : AgreeZ X.y (mzA X.y (Hd.zOf (honMx X i x)) g) (trFull X pl i x (2 * g)) :=
    fun σ r c hz => by
      rw [trFull_cells X pl i x (inShape_of_sizes (inZ_in h C (follows_sizesAt X 0 0) hg hz))
        (by rw [bNo_even X hg]; exact portNo_ne_planes h C hz.1), (listsOf_eq_true X i x).1 g hg]
      rfl
  have hq : (Cm.Seg.ownFF g c).place ∈ Cm.Seg.reads Cm.Seg.Hd.main (2 * g) :=
    Or.inl ⟨g, c, rfl, hg, hc, rfl⟩
  rw [← dict_mz B.lay B.switches B.sized B.sized2 B.p4 g _ c hc, ← libMZ_congr H g]
  show Cm.Seg.at' (libMZ X.y g (mzA X.y (Hd.zOf (honMx X i x)) g)) (Cm.Seg.ownFF g c).place = _
  rw [dict_D5 B.lay B.switches B.sized B.sized2 B.p4 X.hS Cm.Seg.Hd.main (fun _ _ _ => 0) _ hg _ hq,
    Hd.D5_zOf Policy.mainOK B.groups B.full.NHf p0 p1 _ _ (2 * g) (by show 2 * g < 25; omega) _ hq
      ((reads_even_or_own hq).elim id fun e => by rw [e]; omega)]
  exact ((Cm.lay_read_toMat Cm.Seg.Hd.main Policy.mainOK (honAt X i x)).1 g hg c hc).symm

/-- Under the three premises on the public files (Z is in the goals' scope; the goals' reader
returns pp; "publicOf" returns X), g < 12, at every pl, index and request, served or not: at every
valid name of an attention segment the library's reader "cellsA" finds in the trace's attention list
the cell that the honest cells' reading "vAtt g" has there, own or borrowed. The reader's rule of
places, "addrA", is a reading of the verifier's texts; this file ties it to no program. -/
theorem read_att_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) (pl : ℕ → ℕ → ℕ → ℤ) (i : Cm.Idx)
    (x : Instance ppref) {g : ℕ} (hg : g < 12) (c : AttSeg.Raw) (hc : c.Valid DA) :
    cellsA (Hd.shapeA X g) (trFull X pl i x (2 * g + 1)) c = (honAt X i x).vAtt g c := by
  have C := Hd.core_of_scope hZ hR h
  have E := Hd.eleven_of_core h C (Hd.npOf X.hS)
  have hS := E.2.1 g hg
  have hv : c.Valid (dimOf (Hd.shapeA X g)) := by
    rw [dimOf_ref hS, hS.u0]
    exact hc
  show zAt (trFull X pl i x (2 * g + 1)) (addrA (Hd.shapeA X g) c) = _
  unfold zAt
  rw [trFull_cells X pl i x
    (inShape_of_sizes (inside_of_follows h C (follows_sizesAt X 0 0) hg c hv))
    (by rw [bNo_odd]; exact addrA_ne_planes h C hg c hv), (listsOf_eq_true X i x).2.1 g]
  exact (agreeBack g (honMx X i x) hS (E.2.2.2.2 g hg) c hc).symm.trans
    ((Cm.lay_read_toMat Cm.Seg.Hd.main Policy.mainOK (honAt X i x)).2.1 g hg c hc).symm

/-- Under the three premises on the public files (Z is in the goals' scope; the goals' reader
returns pp; "publicOf" returns X), at a position t < 1,024, at every pl, index and request, served
or not: at every feature that holds a cell of hf, hd, hr and of the borrowed stream the library's
reader "Hd.cellsH" finds in the trace's list of the head the cell that the honest cells' reading
"vHead" has there. -/
theorem read_head_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) (pl : ℕ → ℕ → ℕ → ℤ) (i : Cm.Idx)
    (x : Instance ppref) {t : ℕ} (ht : t < Head.nT) :
    (∀ φ < Head.nFeat .hf,
      (Hd.cellsH X.hS X.HLy (borderOf X.y) (trFull X pl i x 24)).hf φ t =
        (honAt X i x).vHead.hf φ t) ∧
    (∀ φ < Head.nFeat .hd,
      (Hd.cellsH X.hS X.HLy (borderOf X.y) (trFull X pl i x 24)).hd φ t =
        (honAt X i x).vHead.hd φ t) ∧
    (∀ φ < Head.nFeat .hr,
      (Hd.cellsH X.hS X.HLy (borderOf X.y) (trFull X pl i x 24)).hr φ t =
        (honAt X i x).vHead.hr φ t) ∧
    ∀ φ < Head.nFeat .x,
      (Hd.cellsH X.hS X.HLy (borderOf X.y) (trFull X pl i x 24)).x φ t =
        (honAt X i x).vHead.x φ t := by
  have C := Hd.core_of_scope hZ hR h
  have B := (Hd.eleven_of_core h C (Hd.npOf X.hS)).1
  obtain ⟨p0, p1⟩ := Hd.parts_ref B.lay B.switches B.sized2
  have N := Hd.numH_of_layout B.full B.head
  have Bd := Hd.borderH_of_layout B.lay B.switches B.sized B.sized2
  have SM := sameMain_cellsH N Bd (agreeH_core h C pl i x) ℤ
  have RA := Hd.readsAtMain_cellsH B.full B.head B.lay B.switches B.sized B.sized2
    (mzA X.y (Hd.zOf (honMx X i x))) (fun _ _ _ => 0) (Hd.mzH X.hS X.y (Hd.zOf (honMx X i x)))
    (fun r _ c _ => by
      show Hd.zOf (honMx X i x) (Hd.labH X.hS X.y (X.hS.NHf + 3)) r c =
        Hd.zOf (honMx X i x) (labA X.y 11 (matIx X.y).iXO) r c
      unfold Hd.labH
      rw [if_pos rfl, B.groups])
  have RT := Policy.readsAtMain_toMat (honAt X i x)
  have D : ∀ n : Cm.Seg.Name, n.Valid Cm.Seg.Hd.main → n.place.1 % 2 = 0 →
      Cm.Seg.at' (Hd.stackedH X.y (mzA X.y (Hd.zOf (honMx X i x))) (fun _ _ _ => 0)
        (Hd.mzH X.hS X.y (Hd.zOf (honMx X i x)))) n.place = Cm.Seg.at' (honMx X i x) n.place :=
    fun n hn h2 => Hd.D5_zOf_name Policy.mainOK B.groups B.full.NHf p0 p1 _ _ n hn h2
  have e24 : 24 % 2 = 0 := rfl
  have e22 : 2 * (12 - 1) % 2 = 0 := rfl
  refine ⟨fun φ hφ => ?_, fun φ hφ => ?_, fun φ hφ => ?_, fun φ hφ => ?_⟩
  · have e := SM.hf φ hφ t ht
    exact (Int.cast_id.symm.trans (e.symm.trans Int.cast_id)).trans
      ((RA.hf φ hφ t ht).trans ((D (.hf φ t) ⟨hφ, ht⟩ e24).trans (RT.hf φ hφ t ht).symm))
  · have e := SM.hd φ hφ t ht
    exact (Int.cast_id.symm.trans (e.symm.trans Int.cast_id)).trans
      ((RA.hd φ hφ t ht).trans ((D (.hd φ t) ⟨hφ, ht⟩ e24).trans (RT.hd φ hφ t ht).symm))
  · have e := SM.hr φ hφ t ht
    exact (Int.cast_id.symm.trans (e.symm.trans Int.cast_id)).trans
      ((RA.hr φ hφ t ht).trans ((D (.hr φ t) ⟨hφ, ht⟩ e24).trans (RT.hr φ hφ t ht).symm))
  · have e := SM.x φ hφ t ht
    exact (Int.cast_id.symm.trans (e.symm.trans Int.cast_id)).trans
      ((RA.x φ hφ t ht).trans ((D (Cm.Seg.ownX φ t)
        ((Cm.lay_own_valid Cm.Seg.Hd.main).2.2 φ hφ t ht) e22).trans (RT.x φ hφ t ht).symm))

/-- **Zeros in a group's list.** Under the three premises on the public files (Z is in the goals'
scope; the goals' reader returns pp; "publicOf" returns X), g < 12, at every pl, index and request:
an entry of a matrix other than b, and other than the borrowed xbI of a later group, is 0 at every
place, inside the shape or outside, where the library's rule "placeOf" puts no valid name's cell. -/
theorem zero_off_ff_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) (pl : ℕ → ℕ → ℕ → ℤ) (i : Cm.Idx)
    (x : Instance ppref) {g : ℕ} (hg : g < 12) {a r c : ℕ} (ha : a ≠ (matIx X.y).iB)
    (hq : 0 < g → a ≠ (matIx X.y).iXI)
    (hn : ∀ q : FFSeg.Cell, q.Valid DF → placeOf X.y DF q ≠ (a, r, c)) :
    trFull X pl i x (2 * g) a r c = 0 := by
  by_cases hI : InShape X (2 * g) a r c
  swap
  · exact trFull_out X pl i x hI
  have C := Hd.core_of_scope hZ hR h
  have B := (Hd.eleven_of_core h C (Hd.npOf X.hS)).1
  obtain ⟨p0, p1⟩ := Hd.parts_ref B.lay B.switches B.sized2
  rw [trFull_cells X pl i x hI (by rw [bNo_even X hg]; exact ha), (listsOf_eq_true X i x).1 g hg]
  show Hd.zOf (honMx X i x) (labA X.y g a) r c = 0
  unfold InShape at hI
  rw [planMats_eq, size_even h C hg] at hI
  obtain ⟨ha9, hr, -⟩ := hI
  have hB : (matIx X.y).iB = 5 := by
    show X.y.parts.getD 0 0 + X.y.parts.getD 1 0 + 1 = 5
    rw [p0, p1]
  have hXI : (matIx X.y).iXI = 8 := by
    show X.y.parts.getD 0 0 + X.y.parts.getD 1 0 + 4 = 8
    rw [p0, p1]
  rw [hB] at ha
  rw [hXI] at hq
  -- the slot t of the library's matrix, and the matrix μ with its part p, that have the number a
  obtain ⟨t, μ, p, ht, hμ, hp, e1, e2, e3, e4⟩ : ∃ (t : ℕ) (μ : FFSeg.Mx) (p : ℕ), t < 8 ∧ μ ≠ .b ∧
      p < partsM X.y (mxNo μ) ∧ Hd.slotNo X.y t = a ∧ portNo X.y t = a ∧
      firstM X.y (mxNo μ) + p = a ∧ (t = 6 → a = 8) := by
    have c : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 6 ∨ a = 7 ∨ a = 8 := by omega
    rcases c with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨0, .af, 0, by norm_num, by decide, by show 0 < X.y.parts.getD 0 0; omega, rfl, rfl,
        rfl, by norm_num⟩
    · exact ⟨1, .af, 1, by norm_num, by decide, by show 1 < X.y.parts.getD 0 0; omega, rfl, rfl,
        rfl, by norm_num⟩
    · exact ⟨2, .af, 2, by norm_num, by decide, by show 2 < X.y.parts.getD 0 0; omega, rfl, rfl,
        rfl, by norm_num⟩
    · exact ⟨3, .ad, 0, by norm_num, by decide, by show 0 < X.y.parts.getD 1 0; omega, p0, p0,
        p0, by norm_num⟩
    · have e : X.y.parts.getD 0 0 + X.y.parts.getD 1 0 = 4 := by rw [p0, p1]
      exact ⟨4, .ar, 0, by norm_num, by decide, Nat.one_pos, e, e, e, by norm_num⟩
    · have e : X.y.parts.getD 0 0 + X.y.parts.getD 1 0 + 2 = 6 := by rw [p0, p1]
      exact ⟨5, .qa, 0, by norm_num, by decide, Nat.one_pos, e, e, e, by norm_num⟩
    · have e : X.y.parts.getD 0 0 + X.y.parts.getD 1 0 + 3 = 7 := by rw [p0, p1]
      exact ⟨7, .xout, 0, by norm_num, by decide, Nat.one_pos, e, e, e, by norm_num⟩
    · have e : X.y.parts.getD 0 0 + X.y.parts.getD 1 0 + 4 = 8 := by rw [p0, p1]
      exact ⟨6, .xin, 0, by norm_num, by decide, Nat.one_pos, e, e, e, fun _ => rfl⟩
  have hmat : mxNo μ ≤ 5 := by cases μ <;> first | exact absurd rfl hμ | decide
  have hr' : r < 65536 := by
    rw [← e3, (entry_eq h C hg hmat hp).1] at hr
    exact lt_of_lt_of_le hr (rowsM_le B.lay B.switches B.sized B.sized2 hμ)
  rw [← e1, Hd.zOf_slot p0 p1 _ hg ht
    (fun h6 => Nat.eq_zero_of_not_pos fun h0 => hq h0 (e4 h6)) r c]
  by_contra hne
  obtain ⟨n, hv, hpl⟩ : ∃ n : Cm.Seg.Name, n.Valid Cm.Seg.Hd.main ∧
      n.place = (2 * g, t * 65536 + r, c) :=
    by_contra fun e => hne (Cm.lay_toMat_off Cm.Seg.Hd.main (honAt X i x) _ e)
  cases n with
  | ff g' q =>
    have f2 : Cm.Seg.plFF q = (t * 65536 + r, c) := congrArg Prod.snd hpl
    refine hn q hv.2.1 ?_
    rw [placeOf_eq_port B.lay B.switches B.sized B.sized2 B.p4 q hv.2.1, f2]
    show (portNo X.y ((t * 65536 + r) / 65536), (t * 65536 + r) % 65536, c) = (a, r, c)
    rw [(slot_div_mod hr').1, (slot_div_mod hr').2, e2]
  | att g' q =>
    have f1 : 2 * g' + 1 = 2 * g := congrArg Prod.fst hpl
    omega
  | hf φ t' =>
    have f1 : 24 = 2 * g := congrArg Prod.fst hpl
    omega
  | hd φ t' =>
    have f1 : 24 = 2 * g := congrArg Prod.fst hpl
    omega
  | hr φ t' =>
    have f1 : 24 = 2 * g := congrArg Prod.fst hpl
    omega

/-- **Zeros in an attention list.** Under the three premises on the public files (Z is in the goals'
scope; the goals' reader returns pp; "publicOf" returns X), g < 12, at every pl, index and request:
an entry of a matrix other than bA and the borrowed qa is 0 at every place, inside the shape or
outside, where the library's rule "addrA" puts no valid name's cell. -/
theorem zero_off_att_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) (pl : ℕ → ℕ → ℕ → ℤ) (i : Cm.Idx)
    (x : Instance ppref) {g : ℕ} (hg : g < 12) {a r c : ℕ}
    (ha : a ≠ (Hd.shapeA X g).cf.NAs + 2) (hq : a ≠ (Hd.shapeA X g).cf.NAs + 3)
    (hn : ∀ q : AttSeg.Raw, q.Valid DA → addrA (Hd.shapeA X g) q ≠ (a, r, c)) :
    trFull X pl i x (2 * g + 1) a r c = 0 := by
  by_cases hI : InShape X (2 * g + 1) a r c
  swap
  · exact trFull_out X pl i x hI
  have C := Hd.core_of_scope hZ hR h
  have E := Hd.eleven_of_core h C (Hd.npOf X.hS)
  have hS := E.2.1 g hg
  obtain ⟨-, -, n1, -⟩ := matsAt_att_gid h C hg
  have PS := planSizes_of_follows h C (follows_sizesAt X 0 0) hg
  have rows : ∀ b < 3, (sizesAt X 0 0 (2 * g + 1)).m b ≤ 65536 := by
    intro b hb
    have c3 : b = 0 ∨ b = 1 ∨ b = 2 := by omega
    rcases c3 with rfl | rfl | rfl
    · rw [PS.asM 0 (by omega), hS.lmS]
      norm_num
    · have e := PS.ahM
      rw [n1, hS.wcH, hS.T] at e
      rw [e]
      norm_num
    · have e := PS.aoM
      rw [n1, hS.wcO, hS.T] at e
      rw [e]
  rw [trFull_cells X pl i x hI (by rw [bNo_odd]; exact ha), (listsOf_eq_true X i x).2.1 g]
  show zsOf (Hd.shapeA X g) g (honMx X i x) a r c = 0
  unfold InShape at hI
  rw [planMats_eq, size_odd h C hg] at hI
  obtain ⟨ha5, hr, -⟩ := hI
  rw [n1] at ha hq
  have ha3 : a < 3 := by omega
  have hr' : r < 65536 := lt_of_lt_of_le hr (rows a ha3)
  rw [zsOf_own1 n1 g _ ha3]
  by_contra hne
  obtain ⟨n, hv, hpl⟩ : ∃ n : Cm.Seg.Name, n.Valid Cm.Seg.Hd.main ∧
      n.place = (2 * g + 1, a * 65536 + r, c) :=
    by_contra fun e => hne (Cm.lay_toMat_off Cm.Seg.Hd.main (honAt X i x) _ e)
  cases n with
  | att g' q =>
    have f1 : 2 * g' + 1 = 2 * g + 1 := congrArg Prod.fst hpl
    obtain rfl : g' = g := by omega
    have hown : Cm.Seg.ownAtt g' q = .att g' q := by
      have ho := hv.2.2
      cases q <;> first | rfl | exact absurd ho Bool.false_ne_true
    have hvd : q.Valid (dimOf (Hd.shapeA X g')) := by
      rw [dimOf_ref hS, hS.u0]
      exact hv.2.1
    obtain ⟨i1, -, i3⟩ := inside_of_follows h C (follows_sizesAt X 0 0) hg q hvd
    have i0 := addrA_ne_planes h C hg q hvd
    rw [PS.NM, n1] at i1
    rw [n1] at i0
    obtain ⟨M1, hM1⟩ : ∃ M1 : Mx, ∀ s' r' c', M1 s' r' c' =
        if (s', r', c') = (2 * g' + 1, a * 65536 + r, c) then (1 : ℤ) else 0 :=
      ⟨_, fun _ _ _ => rfl⟩
    have e : Cm.Seg.at' M1 (Cm.Seg.ownAtt g' q).place =
        zAt (zsOf (Hd.shapeA X g') g' M1) (addrA (Hd.shapeA X g') q) :=
      agreeBack g' M1 hS (E.2.2.2.2 g' hg) q hv.2.1
    rw [hown, hpl] at e
    have e' : M1 (2 * g' + 1) (a * 65536 + r) c =
        zAt (zsOf (Hd.shapeA X g') g' M1) (addrA (Hd.shapeA X g') q) := e
    rw [hM1, if_pos rfl] at e'
    refine hn q hv.2.1 ?_
    generalize addrA (Hd.shapeA X g') q = A at i1 i3 i0 e' ⊢
    obtain ⟨a', r', c'⟩ := A
    have i1' : a' < 1 + 4 := i1
    have i3' : r' < (sizesAt X 0 0 (2 * g' + 1)).m a' := i3
    have i0' : a' ≠ 1 + 2 := i0
    have e2 : (1 : ℤ) = zsOf (Hd.shapeA X g') g' M1 a' r' c' := e'
    by_cases h4 : a' = 4
    · subst h4
      have e4 := zsOf_qa (Hd.shapeA X g') g' M1 r' c'
      rw [n1] at e4
      rw [e4, hM1, if_neg (by
        intro k
        have k1 : 2 * g' = 2 * g' + 1 := congrArg Prod.fst k
        omega)] at e2
      exact absurd e2 one_ne_zero
    · have ha3' : a' < 3 := by omega
      have hr6 : r' < 65536 := lt_of_lt_of_le i3' (rows a' ha3')
      rw [zsOf_own1 n1 g' _ ha3', hM1] at e2
      by_cases k : (2 * g' + 1, a' * 65536 + r', c') = (2 * g' + 1, a * 65536 + r, c)
      · have k2 : a' * 65536 + r' = a * 65536 + r := congrArg (fun z => z.2.1) k
        have k3 : c' = c := congrArg (fun z => z.2.2) k
        obtain rfl : a' = a := by omega
        obtain rfl : r' = r := by omega
        rw [k3]
      · rw [if_neg k] at e2
        exact absurd e2 one_ne_zero
  | ff g' q =>
    have f1 : 2 * g' = 2 * g + 1 := congrArg Prod.fst hpl
    omega
  | hf φ t' =>
    have f1 : 24 = 2 * g + 1 := congrArg Prod.fst hpl
    omega
  | hd φ t' =>
    have f1 : 24 = 2 * g + 1 := congrArg Prod.fst hpl
    omega
  | hr φ t' =>
    have f1 : 24 = 2 * g + 1 := congrArg Prod.fst hpl
    omega

/-- **Zeros in the head's list.** Under the three premises on the public files (Z is in the goals'
scope; the goals' reader returns pp; "publicOf" returns X), at every pl, index and request: an entry
of a matrix other than bH and the borrowed stream is 0 at every place, inside the shape or outside,
where "placeH" puts no feature that holds a cell of hf, hd or hr, at any position. -/
theorem zero_off_head_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) (pl : ℕ → ℕ → ℕ → ℤ) (i : Cm.Idx)
    (x : Instance ppref) {a r c : ℕ} (ha : a ≠ X.hS.NHf + 2) (hq : a ≠ X.hS.NHf + 3)
    (hn : ∀ μ : Head.Mx, μ ≠ .x → ∀ φ < Head.nFeat μ, ∀ t < Head.nT,
      placeH X μ φ t ≠ (a, r, c)) :
    trFull X pl i x 24 a r c = 0 := by
  by_cases hI : InShape X 24 a r c
  swap
  · exact trFull_out X pl i x hI
  have C := Hd.core_of_scope hZ hR h
  have B := (Hd.eleven_of_core h C (Hd.npOf X.hS)).1
  have N := Hd.numH_of_layout B.full B.head
  obtain ⟨q1, q2, q3, -⟩ := head_in h C (follows_sizesAt X 0 0)
  rw [trFull_cells X pl i x hI (by rw [bNo_head]; exact ha), (listsOf_eq_true X i x).2.2]
  show Hd.zOf (honMx X i x) (Hd.labH X.hS X.y a) r c = 0
  unfold InShape at hI
  rw [planMats_eq, size_head h C] at hI
  obtain ⟨ha8, hr, -⟩ := hI
  rw [N.NHf] at ha hq q1 q2 q3
  have ha6 : a < 6 := by omega
  have hr' : r < 65536 := by
    have hr0 : r < (sizesAt X 0 0 24).m a := hr
    by_cases h4 : a < 4
    · rw [(q1 a h4).2.1, N.m] at hr0
      exact hr0
    · by_cases h5 : a = 4
      · subst h5
        rw [q2.2.1, N.mD] at hr0
        omega
      · obtain rfl : a = 5 := by omega
        rw [q3.2.1, N.mR] at hr0
        omega
  unfold Hd.labH
  rw [if_neg (by rw [N.NHf]; omega), B.groups]
  unfold Hd.zOf
  rw [if_pos (by omega), show ((1 + 12) * 256 + a) % 256 = a by omega]
  by_contra hne
  obtain ⟨n, hv, hpl⟩ : ∃ n : Cm.Seg.Name, n.Valid Cm.Seg.Hd.main ∧
      n.place = (24, a * 65536 + r, c) :=
    by_contra fun e => hne (Cm.lay_toMat_off Cm.Seg.Hd.main (honAt X i x) _ e)
  obtain ⟨M1, hM1⟩ : ∃ M1 : Mats ℤ, ∀ a' r' c', M1 a' r' c' =
      if (a', r', c') = (a, r, c) then (1 : ℤ) else 0 := ⟨_, fun _ _ _ => rfl⟩
  have RA := Hd.readsAtMain_cellsH B.full B.head B.lay B.switches B.sized B.sized2
    (fun _ _ r' c' => M1 (X.hS.NHf + 3) r' c') (fun _ _ _ => 0) M1 (fun _ _ _ _ => rfl)
  have one : ∀ m : Cm.Seg.Name, m.place = (24, a * 65536 + r, c) →
      Cm.Seg.at' (Hd.stackedH X.y (fun _ _ r' c' => M1 (X.hS.NHf + 3) r' c') (fun _ _ _ => 0) M1)
        m.place = 1 := by
    intro m hm
    rw [hm]
    show Hd.stackedH X.y _ _ M1 24 (a * 65536 + r) c = 1
    rw [Hd.stackedH_24, show (2 : ℕ) ^ 16 = 65536 by norm_num, (slot_div_mod hr').1,
      (slot_div_mod hr').2, hM1]
    exact if_pos rfl
  have fin : ∀ p : ℕ × ℕ × ℕ, zAt M1 p = 1 → p = (a, r, c) := by
    rintro ⟨p1, p2, p3⟩ e
    have e' : M1 p1 p2 p3 = 1 := e
    rw [hM1] at e'
    by_contra k
    rw [if_neg k] at e'
    exact zero_ne_one e'
  cases n with
  | hf φ t =>
    exact hn .hf (by decide) φ hv.1 t hv.2
      (fin _ ((cellsH_placeH X M1 φ t).1.symm.trans ((RA.hf φ hv.1 t hv.2).trans (one _ hpl))))
  | hd φ t =>
    exact hn .hd (by decide) φ hv.1 t hv.2
      (fin _ ((cellsH_placeH X M1 φ t).2.1.symm.trans ((RA.hd φ hv.1 t hv.2).trans (one _ hpl))))
  | hr φ t =>
    exact hn .hr (by decide) φ hv.1 t hv.2
      (fin _ ((cellsH_placeH X M1 φ t).2.2.1.symm.trans
        ((RA.hr φ hv.1 t hv.2).trans (one _ hpl))))
  | ff g' q =>
    have f1 : 2 * g' = 24 := congrArg Prod.fst hpl
    have f2 : g' < 12 := hv.1
    omega
  | att g' q =>
    have f1 : 2 * g' + 1 = 24 := congrArg Prod.fst hpl
    omega

/-- Under the three premises on the public files (Z is in the goals' scope; the goals' reader
returns pp; "publicOf" returns X): at a request with r < e that is not served, no lists meet "OrdsN"
at the index's matrix of the weights' digits (i.mat) and the request. Of a request with e ≤ r, which
is never served, this says nothing. By "Meaning.tieConstraints". -/
theorem no_lists_of_unserved (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) (i : Cm.Idx) (x : Instance ppref) (hre : x.r < x.e)
    (T : ¬ ServesAt X i x) :
    ¬ ∃ (MG : ℕ → Mats ℤ) (MA : ℕ → Zs) (MH : Mats ℤ),
      OrdsN (layerShape X.P) X.layers.sc X.y X.hS X.HLy (Hd.npOf X.hS) (Hd.polOf X.hS)
        (Hd.shapeA X) i.mat x MG MA MH :=
  fun E => T ((servesAt_iff_in_scope hZ hR h i x).2
    ((tieConstraints Z pp lay X hZ hR h i x).1 ⟨hre, E⟩))

/-- **The bundle holds of the trace.** Under the three premises on the public files (Z is in the
goals' scope; the goals' reader returns pp; "publicOf" returns X), at a request that is served, if
pl has the values 0 and 1 alone: "MeetsAll X i x (trFull X pl i x)". -/
theorem meetsAll_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) {pl : ℕ → ℕ → ℕ → ℤ}
    (h01 : ∀ k r c, pl k r c = 0 ∨ pl k r c = 1) {i : Cm.Idx} {x : Instance ppref}
    (T : ServesAt X i x) : MeetsAll X i x (trFull X pl i x) where
  small := trFull_small_all (lawful_in_scope hZ hR h).1 (lawful_in_scope hZ hR h).2 h01 T
  out _ _ _ _ hI := trFull_out X pl i x hI
  fillG _ hg _ _ _ ha hq hn := zero_off_ff_in_scope hZ hR h pl i x hg ha hq hn
  fillA _ hg _ _ _ ha hq hn := zero_off_att_in_scope hZ hR h pl i x hg ha hq hn
  fillH _ _ _ ha hq hn := zero_off_head_in_scope hZ hR h pl i x ha hq hn
  readG _ hg q hq := read_ff_in_scope hZ hR h pl i x hg q hq
  readA _ hg q hq := read_att_in_scope hZ hR h pl i x hg q hq
  readH _ ht := read_head_in_scope hZ hR h pl i x ht
  ords := ordsN_in_scope hZ hR h pl T
  keysG _ hg tokv := forIn_layers_in_scope hZ hR h pl T tokv hg
  keysA _ hg := forIn_att_in_scope hZ hR h pl T hg
  keysH _ e1 e2 Rq := forIn_head_in_scope hZ hR h pl T e1 e2 Rq

/-- **Every value of "traceFull" meets the bundle.** Under the three premises on the public files (Z
is in the goals' scope; the goals' reader returns pp; "publicOf" returns X), if pl has the values 0
and 1 alone: if "traceFull X pl i x" has the value T, then "MeetsAll X i x T". Where it has none the
request is not served ("traceFull_eq_none_iff", Johnson/HonestTrace/Full.lean). -/
theorem meetsAll_of_traceFull (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) {pl : ℕ → ℕ → ℕ → ℤ}
    (h01 : ∀ k r c, pl k r c = 0 ∨ pl k r c = 1) {i : Cm.Idx} {x : Instance ppref} {T : Tr}
    (e : traceFull X pl i x = some T) : MeetsAll X i x T := by
  obtain ⟨hS, rfl⟩ := (traceFull_eq_some_iff X pl i x T).1 e
  exact meetsAll_in_scope hZ hR h h01 hS

/-- Under the three premises on the public files (Z is in the goals' scope; the goals' reader
returns pp; "publicOf" returns X): the numbers of parts are the reference's: af lies in 3 parts, ad
in 1, as in 1 for every group below 12, hf in 4. -/
theorem parts_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) :
    X.y.parts.getD 0 0 = 3 ∧ X.y.parts.getD 1 0 = 1 ∧ (∀ g < 12, (Hd.shapeA X g).cf.NAs = 1) ∧
      X.hS.NHf = 4 := by
  have C := Hd.core_of_scope hZ hR h
  have B := (Hd.eleven_of_core h C (Hd.npOf X.hS)).1
  obtain ⟨p0, p1⟩ := Hd.parts_ref B.lay B.switches B.sized2
  exact ⟨p0, p1, fun g hg => (matsAt_att_gid h C hg).choose_spec.2.1, B.full.NHf⟩

/-- **The reader by labels finds the matrix with the name's number.** Under the three premises on
the public files (Z is in the goals' scope; the goals' reader returns pp; "publicOf" returns X), for
every trace T, every segment σ of a proof with 12 groups and every name μ that has the number a in
σ's list: "cellOf X T" at σ's number and μ's label is the image in the field of the entry of T at
σ's number and a. -/
theorem cellOf_label_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) (T : Tr) {σ : Seg} (hσ : σ.Below 12) {μ : MatName}
    {a : ℕ} (ha : noAt X σ μ = some a) (r c : ℕ) :
    cellOf X T (σ.no 12) μ.label r c = ((T (σ.no 12) a r c : ℤ) : Cb.Gl.F) := by
  obtain ⟨p0, p1, pA, pH⟩ := parts_in_scope hZ hR h
  have hf : MatName.ofLabel? (X.y.parts.getD 0 0) (X.y.parts.getD 1 0)
      (Hd.shapeA X (σ.no 12 / 2)).cf.NAs X.hS.NHf σ μ.label = some μ := by
    have hm := MatName.mem_all_of_no? ha
    rw [p0, p1, pH] at hm ⊢
    cases σ with
    | ff g => exact MatName.ofLabel?_label_ref (.ff g) μ hm
    | att g =>
      have hg : g < 12 := hσ
      have e : Seg.no 12 (.att g) / 2 = g := by
        show (2 * g + 1) / 2 = g
        omega
      rw [e, pA g hg] at hm ⊢
      exact MatName.ofLabel?_label_ref (.att g) μ hm
    | head => exact MatName.ofLabel?_label_ref .head μ hm
  unfold cellOf
  rw [Seg.ofNo_no hσ]
  simp only
  rw [hf]
  simp only
  unfold byName
  rw [if_pos (Seg.ofNo_no hσ), ha]

/-- **In a group's plan the entries bear the labels.** Under the three premises on the public files
(Z is in the goals' scope; the goals' reader returns pp; "publicOf" returns X), g < 12: if the name
μ has the number a in the list of the feed-forward segment of group g, then entry a of the
verifier's plan of that sub-proof has the name "μ.label". -/
theorem planName_ff_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) {g : ℕ} (hg : g < 12) {μ : MatName} {a : ℕ}
    (ha : noAt X (.ff g) μ = some a) :
    ((planMats X (2 * g)).getD a {}).name = μ.label := by
  have C := Hd.core_of_scope hZ hR h
  have B := (Hd.eleven_of_core h C (Hd.npOf X.hS)).1
  obtain ⟨p0, p1⟩ := Hd.parts_ref B.lay B.switches B.sized2
  obtain ⟨sc, rope, wsLay, V, tokv, set, hP, hG⟩ := Hd.public_plans h
  obtain ⟨P, e⟩ := planG_there h C hg
  have nms : (P.tl.mats.map fun M => M.name) =
      #["af0", "af1", "af2", "ad0", "ar", "b", "qa", "xbO", "xbI"] := by
    rw [plan_names hP hG g P e, tails_names X.y (by rw [B.groups]; exact hg)]
    unfold asksTab
    rw [p0, p1]
    rfl
  have at' : ∀ b : ℕ, ((planMats X (2 * g)).getD b {}).name =
      (#["af0", "af1", "af2", "ad0", "ar", "b", "qa", "xbO", "xbI"] : Array String).getD b "" := by
    intro b
    rw [planMats_eq, matsAt_even hg e, ← nms]
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map]
    cases P.tl.mats[b]? <;> rfl
  unfold noAt at ha
  rw [p0, p1] at ha
  rw [at']
  cases μ <;> simp only [MatName.no?] at ha
  case af p =>
    split at ha
    · rename_i hp
      obtain rfl := Option.some.inj ha
      have c3 : p = 0 ∨ p = 1 ∨ p = 2 := by omega
      rcases c3 with rfl | rfl | rfl <;> decide
    · exact absurd ha (by simp)
  case ad p =>
    split at ha
    · rename_i hp
      obtain rfl := Option.some.inj ha
      obtain rfl : p = 0 := Nat.lt_one_iff.1 hp
      decide
    · exact absurd ha (by simp)
  case ar =>
    obtain rfl := Option.some.inj ha
    decide
  case b =>
    obtain rfl := Option.some.inj ha
    decide
  case qa =>
    obtain rfl := Option.some.inj ha
    decide
  case xbO =>
    obtain rfl := Option.some.inj ha
    decide
  case xbI =>
    obtain rfl := Option.some.inj ha
    decide
  all_goals exact absurd ha (by simp)

/-- **In an attention sub-proof's plan the entries bear the labels.** Under the three premises on
the public files (Z is in the goals' scope; the goals' reader returns pp; "publicOf" returns X), g <
12: if the name μ has the number a in the list of the attention segment of group g, then entry a of
the verifier's plan of that sub-proof has the name "μ.label". -/
theorem planName_att_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) {g : ℕ} (hg : g < 12) {μ : MatName} {a : ℕ}
    (ha : noAt X (.att g) μ = some a) :
    ((planMats X (2 * g + 1)).getD a {}).name = μ.label := by
  obtain ⟨i, -, n1, e⟩ := matsAt_att_gid h (Hd.core_of_scope hZ hR h) hg
  have e2 : Seg.no 12 (.att g) / 2 = g := by
    show (2 * g + 1) / 2 = g
    omega
  unfold noAt at ha
  rw [e2, n1] at ha
  rw [planMats_eq, e]
  have nm : ∀ (b : ℕ) (M : Model.TMat), (Attention.matrices (Hd.shapeA X g) i)[b]? = some M →
      (((Attention.matrices (Hd.shapeA X g) i).map fixed).getD b {}).name = M.name := by
    intro b M hM
    have e3 : ((Attention.matrices (Hd.shapeA X g) i).map fixed)[b]? = some (fixed M) := by
      rw [Array.getElem?_map, hM]
      rfl
    rw [getD_of e3]
    unfold fixed
    split <;> rfl
  have tl := matrices_tail (Hd.shapeA X g) i
  rw [n1] at tl
  have as0 : (Attention.matrices (Hd.shapeA X g) i)[0]? = some (Attention.ownMatrix i
      ("as" ++ toString 0) (2 ^ (Hd.shapeA X g).cf.lmS)
      ((Hd.shapeA X g).kAs / (Hd.shapeA X g).cf.NAs) 0 i.wpS) := by
    unfold Attention.matrices
    rw [Array.getElem?_append_left (by simp [n1])]
    simp [n1]
  cases μ <;> simp only [MatName.no?] at ha
  case as p =>
    split at ha
    · rename_i hp
      obtain rfl := Option.some.inj ha
      obtain rfl : p = 0 := Nat.lt_one_iff.1 hp
      exact nm 0 _ as0
    · exact absurd ha (by simp)
  case ah =>
    obtain rfl := Option.some.inj ha
    exact nm 1 _ (tl 0)
  case ao =>
    obtain rfl := Option.some.inj ha
    exact nm (1 + 1) _ (tl 1)
  case bA =>
    obtain rfl := Option.some.inj ha
    exact nm (1 + 2) _ (tl 2)
  case qa =>
    obtain rfl := Option.some.inj ha
    exact nm (1 + 3) _ (tl 3)
  all_goals exact absurd ha (by simp)

/-- **In the head's plan the entries bear the labels.** Under the three premises on the public files
(Z is in the goals' scope; the goals' reader returns pp; "publicOf" returns X): if the name μ has
the number a in the head's list, then entry a of the verifier's plan of the head has the name
"μ.label".
-/
theorem planName_head_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) {μ : MatName} {a : ℕ} (ha : noAt X .head μ = some a) :
    ((planMats X 24).getD a {}).name = μ.label := by
  have C := Hd.core_of_scope hZ hR h
  have B := (Hd.eleven_of_core h C (Hd.npOf X.hS)).1
  have hN : X.hS.NHf = 4 := B.full.NHf
  obtain ⟨H0, hH, e⟩ := (Hd.publicH_of_public h).plan
  obtain ⟨stream, -, hm⟩ := Hd.planH2_label hH
  have em : matsAt X 24 = Model.Head.matsH X.hS X.HLy (borderOf X.y) (1 + X.y.NGr) stream.aId := by
    rw [matsAt_head, e]
    exact hm
  unfold noAt at ha
  rw [hN] at ha
  rw [planMats_eq, em]
  unfold Model.Head.matsH
  rw [hN]
  cases μ <;> simp only [MatName.no?] at ha <;>
    first
      | (obtain rfl := Option.some.inj ha; rfl)
      | (split at ha
         · rename_i p hp
           obtain rfl := Option.some.inj ha
           have c4 : p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3 := by omega
           rcases c4 with rfl | rfl | rfl | rfl <;> rfl
         · exact absurd ha (by simp))
      | exact absurd ha (by simp)

/-- **A guard: the trace can be packed.** Under the three premises on the public files (Z is in the
goals' scope; the goals' reader returns pp; "publicOf" returns X), at a request that is served, if
pl has the values 0 and 1 alone, for sizes s that follow X's plans with the radix 2^20 and the shift
2^17 ("sizesAt X (2^20) (2^17)" is such a family: "follows_sizesAt"): at each of the 25 sub-proofs
the messages "msgOf s" of the trace are a packing of small integers ("BaseSeg"), and "ownAt" reads
back from them the sub-proof's whole list in the trace, borrowed matrices too, at all numbers, rows
and columns. The seats are "seat0",
one message for each label: they are made for such guards (Johnson/Goal/Meaning/HidPack.lean) and
are not the byte format's seating, so this says nothing of a prover's messages. -/
theorem packs_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) {pl : ℕ → ℕ → ℕ → ℤ}
    (h01 : ∀ k r c, pl k r c = 0 ∨ pl k r c = 1) {i : Cm.Idx} {x : Instance ppref}
    (T : ServesAt X i x) {s : ℕ → Size} (Fo : Follows X s) (hb : ∀ k < 25, (s k).beta = 2 ^ 17)
    (hr : ∀ k < 25, (s k).rad = 2 ^ 20) :
    ∀ k < 25, BaseSeg s (seatBy seat0 X s) (msgOf s (trFull X pl i x)) k ∧
      ownAt s (seatBy seat0 X s) (msgOf s (trFull X pl i x)) k = trFull X pl i x k := by
  intro k hk
  have C := Hd.core_of_scope hZ hR h
  obtain ⟨w, Mh, -, M, -, -⟩ :=
    trace_of_true hZ hR h i x ((servesAt_iff_in_scope hZ hR h i x).1 T)
  have O0 := ownSame_seenC h C Fo M hk
  obtain ⟨b1, b2, b3⟩ := borrowed_core h C pl i x
  have O : OwnSame X s (trFull X pl i x) k := by
    refine ⟨O0.rad, O0.m, fun a ha r _ c _ => ?_⟩
    have ha' : a < (matsAt X k).size := by
      rw [← Fo.NM k hk]
      exact ha
    rcases owner_cases h C hk ha' with ⟨o1, o2⟩ | ⟨g, h0, hg, rfl, rfl, o1, o2⟩ |
      ⟨g, hg, rfl, rfl, o1, o2⟩ | ⟨rfl, rfl, o1, o2⟩
    · rw [o1, o2]
    · rw [o1, o2]
      exact (b1 g h0 hg r c).symm
    · rw [o1, o2]
      exact (b2 g hg r c).symm
    · rw [o1, o2]
      exact (b3 r c).symm
  have sm : ∀ a < (s k).NM, ∀ r < (s k).m a, ∀ c < (s k).k a,
      |trFull X pl i x k a r c| < 2 * ((s k).beta : ℤ) := fun a _ r _ c _ => by
    rw [hb k hk]
    have e : (2 : ℤ) * ((2 ^ 17 : ℕ) : ℤ) = 2 ^ 18 := by norm_num
    rw [e]
    exact lt_trans (trFull_small_all (lawful_in_scope hZ hR h).1 (lawful_in_scope hZ hR h).2 h01 T
      k a r c) (by norm_num)
  have U := Cb.Pv.Tail.uniq_gl (hb k hk) (hr k hk)
  refine ⟨baseSeg_msgOf Cb.Gl.p U sm O, (ownAt_msgOf Cb.Gl.p U sm O).trans ?_⟩
  funext a r c
  by_cases hI : a < (s k).NM ∧ c < (s k).k a ∧ r < (s k).m a
  · exact mzTot_cutOf (s k) _ hI.1 hI.2.1 hI.2.2
  · have h0 : trFull X pl i x k a r c = 0 := by
      refine trFull_out X pl i x fun H => hI ?_
      unfold InShape at H
      rw [planMats_eq] at H
      exact ⟨by rw [Fo.NM k hk]; exact H.1, by rw [Fo.k k hk a H.1]; exact H.2.2,
        by rw [Fo.m k hk a H.1]; exact H.2.1⟩
    rw [h0]
    unfold mzTot
    split_ifs with h1 h2 h3
    · exact absurd ⟨h1, h2, h3⟩ hI
    all_goals rfl

end Scope

/-! ## A guard on the premises -/

/-- **A guard: the premises of "meetsAll_in_scope" on files, index and request can be met together,
if "publicOf" returns.** For every lay and X: if "publicOf" returns X at the stored full-size
example's parameter file and scale file, then these files are in the goals' scope, the goals' reader
returns some pp, and some index serves at X some request with r = 1,023 and e = 1,024, which has no
counted position. (In the proof all weights and all tokens are 0; the statement does not keep that.)
That "publicOf" returns there is not shown. -/
theorem premises_met_of_public (lay : Option ByteArray) (X : Model.Verify.Public)
    (h : publicOf VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL lay = .ok X) :
    ∃ (pp : ScalesAndPolicy) (i : Cm.Idx) (x : Instance ppref), VerifierAndGoals.InScope VerifierAndGoals.storedPublicFiles = true ∧
      VerifierAndGoals.readFiles VerifierAndGoals.storedPublicFiles = .ok pp ∧ x.r = 1023 ∧ x.e = 1024 ∧
      ServesAt X i x := by
  obtain ⟨pp, hR, -⟩ := VerifierAndGoals.filesRead.full.2
  exact ⟨pp, _, _, VerifierAndGoals.inScope_full, hR, rfl, rfl,
    serves_met (lawful_in_scope VerifierAndGoals.inScope_full hR h).1 _⟩

end OnBytes.HonestTrace

#print axioms OnBytes.HonestTrace.planMats_eq
#print axioms OnBytes.HonestTrace.inShape_of_sizes
#print axioms OnBytes.HonestTrace.cut_eq_cutOf
#print axioms OnBytes.HonestTrace.placeOf_eq_port
#print axioms OnBytes.HonestTrace.rowsM_le
#print axioms OnBytes.HonestTrace.zsOf_own1
#print axioms OnBytes.HonestTrace.entry_eq
#print axioms OnBytes.HonestTrace.portNo_ne_planes
#print axioms OnBytes.HonestTrace.addrA_ne_planes
#print axioms OnBytes.HonestTrace.trFull_pair
#print axioms OnBytes.HonestTrace.borrowed_core
#print axioms OnBytes.HonestTrace.agreeH_core
#print axioms OnBytes.HonestTrace.ordsN_core
#print axioms OnBytes.HonestTrace.servesAt_iff_in_scope
#print axioms OnBytes.HonestTrace.lawful_in_scope
#print axioms OnBytes.HonestTrace.small_off_planes_in_scope
#print axioms OnBytes.HonestTrace.borrowed_in_scope
#print axioms OnBytes.HonestTrace.ordsN_in_scope
#print axioms OnBytes.HonestTrace.r0_in_scope
#print axioms OnBytes.HonestTrace.forIn_att_in_scope
#print axioms OnBytes.HonestTrace.forIn_head_in_scope
#print axioms OnBytes.HonestTrace.forInG_of_keys_in_scope
#print axioms OnBytes.HonestTrace.forIn_layers_in_scope
#print axioms OnBytes.HonestTrace.read_ff_in_scope
#print axioms OnBytes.HonestTrace.read_att_in_scope
#print axioms OnBytes.HonestTrace.read_head_in_scope
#print axioms OnBytes.HonestTrace.zero_off_ff_in_scope
#print axioms OnBytes.HonestTrace.zero_off_att_in_scope
#print axioms OnBytes.HonestTrace.zero_off_head_in_scope
#print axioms OnBytes.HonestTrace.no_lists_of_unserved
#print axioms OnBytes.HonestTrace.meetsAll_in_scope
#print axioms OnBytes.HonestTrace.premises_met_of_public
#print axioms OnBytes.HonestTrace.meetsAll_of_traceFull
#print axioms OnBytes.HonestTrace.parts_in_scope
#print axioms OnBytes.HonestTrace.cellOf_label_in_scope
#print axioms OnBytes.HonestTrace.bordersOf_names
#print axioms OnBytes.HonestTrace.plan_names
#print axioms OnBytes.HonestTrace.tails_names
#print axioms OnBytes.HonestTrace.planName_ff_in_scope
#print axioms OnBytes.HonestTrace.planName_att_in_scope
#print axioms OnBytes.HonestTrace.planName_head_in_scope
#print axioms OnBytes.HonestTrace.packs_in_scope
