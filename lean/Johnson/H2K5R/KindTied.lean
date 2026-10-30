-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/H2K5R/KindTied.lean: THE KIND K5's SHARE OF THE CHAIN OF PROMISES, AT
THE PROOF FILE's WRITTEN DESCRIPTION, IN THE GOALS' SCOPE: KindTied
(Johnson/Desc/Sound/TiedPlaces.lean) at the kind K5, at the table's written lists: linksFull
(Johnson/Desc/Sound/AtDriver.lean) and flatPlacesOf linksFull true. After the pattern of
k03_kindTied (Johnson/P5K3R/SitsKinds.lean).

IT IS A FRAME, NOT A ROW THAT COUNTS. The form that counts has, in front of KindTied, the scope,
"the verifier's own value is laid", and a closed list of named tests on the plan. Here no such test
shows: whatever the payers of K5Owed will ask (tests and facts that are no tests) sits inside the
premise H. One theorem is owed: K5Owed at each of the twelve groups, at the one filling of the
table's meaning, with that list in front.

Why. The field of the chain of promises is had kind by kind (eachTied_of_kinds). The table's two
lists are letters of the tie (K05_tied_at, TiedAtEntry.lean): at the written lists every test
on the table alone is a closed term, which the kernel decides. What ties the table's number to the
description's flat list is the number: in scope the entry at link l, hearing block i, stands at 14 l
+ i + 2 (IM.flatIx_scope).

Main names:
  `k5AllB`, `k5AllB_full`, `k05_places_full`: in the written list of places the kind K5 stands at
    the numbers 14 (2 g + 1) + 4, g below 12, with the place ⟨1, some (2 g + 1), 3, K5⟩, and nowhere
    else.
  `linksFull_att`: the written list has attention at 2 g + 1. `ridersAll_full`, `riders_full`: the
    kind's test on what rides says yes at the twelve numbers.
  These are decided by the kernel, AT ONE VERSION OF THE TABLE: Johnson/Desc/First/Borders.lean
    as this library has it. At another version they would have to be decided again.
  `K5OwedT`: what is owed at one group on the table and its meaning: on the table's numbers: K5Book;
    what the row asks is open; and, at some filling of the law's letters, the meaning K5AtMg (nine
    fields). The law's letters stand under an ∃: none of them occurs in the tie, so the payer picks
    them.
  `K5Owed`: **what is still owed at one group**, as one proposition: on the piece q at the number:
    nothing is put behind its rounds; its error is the cap; its stretch is, round by round, the data
    of its own block's declared rounds; and K5OwedT.
  `k05_kindTied`: **in scope, from an opening at the second hash function, F.planOk, the door's yes
    and OfDesc: where readsOpen and rowsApart say yes at the written lists, the extractor lays
    nothing at the twelve numbers, and K5Owed holds at each of the twelve groups: KindTied N Mg
    linksFull (flatPlacesOf linksFull true) E (T.p₁ :: T.l₁) K5.**
THE TWO TESTS readsOpen AND rowsApart ARE PREMISES HERE, THOUGH CLOSED TERMS: they stand as
theorems (reads_full, apart_full: Johnson/Desc/Sound/K6Fifth.lean) in a file that is not imported
here; no second copy is typed.
WHAT IS LEFT, ALL OF IT: OfDesc; these two; the extractor; K5Owed's six (K5AtMg counted as one). The
full size alone: the scope is the goals'; the small written list has no fellow here. Whether K5Owed
can be met is shown nowhere: no member. Most fields of K5AtMg are fenced by the table's promise: at
a meaning whose promise never holds they are idle, and the tie with them: a member counts only at
the one filling of the table's meaning. OVER WHAT IT STANDS: all that TiedAtEntry.lean's head
names.
No soundness of the protocol is claimed: the premises named are not shown.
Nothing is claimed on completeness or hiding.

-/
import Johnson.H2K5R.TiedAtEntry
import Johnson.IMR.FlatScope
import Johnson.Desc.Sound.TiedPlaces

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb IOR TWhole Cb.Fo Cb.LdLkp Cb.Pv.Att Cb.Pv.Att.End Inst.Model Inst.Model.AttSeg
open OnBytes OnBytes.Model OnBytes.Model.Road
open OnBytes.Slice OnBytes.Flat OnBytes.Maker Run Fo.Peel KObj
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc.First.Look (Sent attCaller attSg JAtt AttOK enMask lookAt)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc (Claim RoundAsG Block Place Chain Link FileDescription KindName)
open VerifiableInference.Desc.First (ModelPart Meaning Numbers start flatPlaces flatPlacesOf)

/-- The test over a list of places: every entry of the kind K5 stands at a number 14 (2 g + 1) + 4,
g
below 12, and is that segment's piece 3. -/
def k5AllB (ps : List Place) : Bool :=
  (List.range ps.length).all fun i =>
    match ps[i]? with
    | some a => a.kind != KindName.K5 ||
        (List.range 12).any fun g =>
          i == 14 * (2 * g + 1) + 4 && Decidable.decide (a = ⟨1, some (2 * g + 1), 3, .K5⟩)
    | none => true

set_option maxRecDepth 1000000 in
theorem k5AllB_full : k5AllB (flatPlacesOf linksFull true) = true := by decide +kernel

/-- **Where the kind stands in the full list of places.** -/
theorem k05_places_full (i : ℕ) (a : Place) (ha : (flatPlacesOf linksFull true)[i]? = some a)
    (hk : a.kind = KindName.K5) :
    ∃ g, g < 12 ∧ i = 14 * (2 * g + 1) + 4 ∧ a = ⟨1, some (2 * g + 1), 3, .K5⟩ := by
  have hi : i < (flatPlacesOf linksFull true).length := (List.getElem?_eq_some_iff.1 ha).1
  have h := List.all_eq_true.1 k5AllB_full i (List.mem_range.2 hi)
  rw [ha] at h
  have h2 : ((List.range 12).any fun g =>
      i == 14 * (2 * g + 1) + 4 && Decidable.decide (a = ⟨1, some (2 * g + 1), 3, .K5⟩)) =
      true := by
    rcases (Bool.or_eq_true _ _).mp h with h1 | h1
    · rw [hk] at h1
      exact absurd h1 (by decide)
    · exact h1
  obtain ⟨g, hg, h3⟩ := List.any_eq_true.1 h2
  obtain ⟨h5, h6⟩ := (Bool.and_eq_true _ _).mp h3
  exact ⟨g, List.mem_range.1 hg, by simpa using h5, of_decide_eq_true h6⟩

theorem linksFull_att (g : ℕ) (hg : g < 12) : linksFull[2 * g + 1]? = some .attention := by
  have h : ((List.range 12).all fun g =>
      Decidable.decide (linksFull[2 * g + 1]? = some ModelPart.attention)) =
      true := by decide
  exact of_decide_eq_true (List.all_eq_true.1 h g (List.mem_range.2 hg))

set_option maxRecDepth 1000000 in
theorem ridersAll_full : ((List.range 12).all fun g =>
    ridersB linksFull (flatPlacesOf linksFull true) (14 * (2 * g + 1) + 4) (2 * g + 1)) = true := by
  decide +kernel

theorem riders_full (g : ℕ) (hg : g < 12) :
    ridersB linksFull (flatPlacesOf linksFull true) (14 * (2 * g + 1) + 4) (2 * g + 1) = true :=
  List.all_eq_true.1 ridersAll_full g (List.mem_range.2 hg)

open Classical in
/-- **What is owed at one group on the table and its meaning**: Wv: the public parameters; before:
the
block's list of commitments; a, x, xd: the group's plan and the places of the segment's two lookups;
links, ps, k: the table's two lists and the number; q: the piece at that number. -/
def K5OwedT {W : Type} {Fr : Frame} (Wv : Verify.Public) (g : ℕ) (before : List (ℕ × ℕ))
    (a : Attention.Plan) (x xd : VerifiableInference.Desc.First.Look.Place) (links : List ModelPart)
    (ps : List Place) (k : ℕ) (N : Numbers) (Mg : Meaning ProofFile.InstPub W)
    (q : Sound.Piece (ckP .two) Fr (ProofFile.InstPub × First.S) Claim W) : Prop :=
  K5Book N ⟨1, some (2 * g + 1), 3, .K5⟩ ⟨1, some (2 * g + 1), 4, .K1⟩ ∧
  (∀ t ∈ (pubRowOf links ⟨1, some (2 * g + 1), 3, .K5⟩).asks,
    t ∈ (pubSets Mg.more links ps)[k]?.getD []) ∧
  ∃ (Cl' : Type) (claim : Aff → Cl') (Ds : Sent) (rad : OracleShape → Nat) (Ex : Iop.ExtSpec)
    (Wp : Type) (α : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns a.seam.tl)) → Cb.Gl.E) (ns : ℕ)
    (tj : OnBytes.K.Kc.Tape)
    (x0 : ProofFile.InstPub → First.S × Fr.E.Str →
      TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns a.seam.tl)))
    (_ : First.S × Fr.E.Str → Ex.Str) (gOf : ProofFile.InstPub → First.S × Fr.E.Str → Forest.Heard)
    (plJ : ℕ → ℕ → JAtt x.ns a.seam.tl)
    (I : PinItemP Fr seatSO q.base W (attSg x Ds rad).Msg) (arr : Array (ℕ × String)),
    K5AtMg q.base claim Wv (2 * g + 1) before a x Ds rad Ex Wp α ns tj x0 gOf plJ I
      (fun π => relAt (meansQ N Mg fun s => (π, s)) (outsQ links ps k))
      N Mg links ⟨1, some (2 * g + 1), 3, .K5⟩ ((openSets links ps (start links))[k]?.getD [])
      ((pubSets Mg.more links ps)[k]?.getD [])
      (Look.P.ofPlace (Params.settingOf Wv.P.frame) false x)
      (Look.P.ofPlace (Params.settingOf Wv.P.frame) true xd) arr (Forest.elems a.fs) a.ns

/-- **What is still owed at one group**: on the piece q: nothing is put behind its rounds; its error
is
the cap; its stretch is, round by round, the data of its own block's declared rounds; and K5OwedT.
-/
def K5Owed {W : Type} {Fr : Frame} (Wv : Verify.Public) (g : ℕ) (before : List (ℕ × ℕ))
    (a : Attention.Plan) (x xd : VerifiableInference.Desc.First.Look.Place) (links : List ModelPart)
    (ps : List Place) (k : ℕ) (N : Numbers) (Mg : Meaning ProofFile.InstPub W)
    (q : Sound.Piece (ckP .two) Fr (ProofFile.InstPub × First.S) Claim W) : Prop :=
  q.back = [] ∧ q.err = Err.cap 128 (uLT (ckP .two) q.ds) ∧
  (∃ num : Fmt.TreeSource → ℕ,
    List.Forall₂ (fun d r => VerifiableInference.Desc.Sound.RoundIs num r d) q.ds q.b.rounds) ∧
  K5OwedT Wv g before a x xd links ps k N Mg q

/-- **THE KIND K5's SHARE, AT THE PROOF FILE's WRITTEN DESCRIPTION.** -/
theorem k05_kindTied {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block First.S Claim)}
    {c : Chain First.S Claim} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hpl : F.planOk = true)
    {D : WholeD} (hs : ∀ t ∈ LPFD.lawsAsk OnBytes.secondHashFunction P.pol lay P.KL F D, t.2 = true)
    {D' : WholeD} {all : List LeftT} {X₁ X₂ W : Type}
    {T : ThreeAt (ckP .two) D' all
      (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c)
      X₁ X₂ W}
    (hT : OfDesc _ T) (N : Numbers) (Mg : Meaning ProofFile.InstPub W)
    (E : ℕ → (ProofFile.InstPub × First.S) × (Sound.frameAt D' all D'.key₁ T.ft₁).E.Str →
      (ProofFile.InstPub × First.S) × (Sound.frameAt D' all D'.key₁ T.ft₁).E.Str → W → W)
    (hr : readsOpen linksFull (flatPlacesOf linksFull true) (start linksFull) = true)
    (hap : rowsApart linksFull (flatPlacesOf linksFull true) = true)
    (hE : ∀ g, g < 12 → ∀ u v w, E (14 * (2 * g + 1) + 4) u v w = w)
    (H : ∀ g, g < 12 → ∀ a x xd q, Bs.G₀.W.A[g]? = some a →
      lookAt Bs.G₀.W (2 * g + 1) false = some x → lookAt Bs.G₀.W (2 * g + 1) true = some xd →
      (T.p₁ :: T.l₁)[14 * (2 * g + 1) + 4]? = some q →
      K5Owed Bs.G₀.W g ((H2K5.k5Before? Z ("A" ++ toString g)).getD []) a x xd linksFull
        (flatPlacesOf linksFull true) (14 * (2 * g + 1) + 4) N Mg q) :
    KindTied N Mg linksFull (flatPlacesOf linksFull true) E (T.p₁ :: T.l₁) KindName.K5 := by
  intro i q a hq ha hk
  obtain ⟨g, hg, rfl, rfl⟩ := k05_places_full i a ha hk
  obtain ⟨h4, g', hg', e⟩ := att_only O.pub O.blank (IM.subs_att hS hR O.pub O.blank hg)
  obtain rfl : g' = g := by omega
  obtain ⟨Lk, Eb, -, e1, e2, -, -⟩ := k5_alone O h4 hg'
  have hfl0 := IM.hear_at_flat e1 e2
  have hfl : c.blocksInOrder[14 * (2 * g' + 1) + 4]? = some Eb := by
    have e3 := IM.flatIx_scope hS hR O (l := 2 * g' + 1) (by omega) 2
    rw [e3, show 14 * (2 * g' + 1) + 2 + 2 = 14 * (2 * g' + 1) + 4 by omega] at hfl0
    exact hfl0
  obtain ⟨sv, hfp', -, hk0, -⟩ := K05_place_at O h4 hg'
  have eP : Eb.place = ⟨1, some (2 * g' + 1), 3, .K5⟩ := by
    rw [← hfp', List.getElem?_map, IM.hear_at_flat e1 e2] at hk0
    exact Option.some.inj hk0
  obtain ⟨g2, a, x, xd, -, -, eP2, ea, hx, hxd, Ht⟩ :=
    K05_tied_at O hpl hs hfl (by rw [eP])
  obtain rfl : g2 = g' := by
    have e4 : (some (2 * g2 + 1) : Option ℕ) = some (2 * g' + 1) :=
      congrArg Place.link (eP2.symm.trans eP)
    have e5 := Option.some.inj e4
    omega
  obtain ⟨hb, he, ⟨num, hrd⟩, Bk, hQ, Cl', claim, Ds, rad, Ex, Wp, α, ns, tj, x0, yOf, gOf, plJ, I,
    arr, Hm⟩ := H g2 hg a x xd q ea hx hxd hq
  exact (Ht linksFull _ (linksFull_att g2 hg) ha (k5_next_place _ _ ha) hT hq hb he num hrd claim Ds
    rad Ex Wp α ns tj x0 yOf gOf plJ I N Mg arr Bk hQ hr hap
    (riders_full g2 hg) Hm (E _) (hE g2 hg)).tiedAt

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.k5AllB_full
#print axioms VerifiableInference.Desc.First.Att.P.k05_places_full
#print axioms VerifiableInference.Desc.First.Att.P.linksFull_att
#print axioms VerifiableInference.Desc.First.Att.P.riders_full
#print axioms VerifiableInference.Desc.First.Att.P.k05_kindTied
