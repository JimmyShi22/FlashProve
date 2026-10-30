-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/HbAtHead.lean: THE PREMISE hb OF THE CLAUSE "entsJoin" (EntsHead.lean,
EntsHeadAt.lean: "the form in which the key side of the lookup on the calls ends names no entry")
FROM THE LOOKUPS' PROMISE ON THE STATE; AND WHAT THAT PROMISE SAYS OF THE HEARD VALUE's SHAPE.
Statements and proofs: projections.

The lookups' promise `K3LeftOn fork heard h lm first Q s` (Johnson/Top/H/K3LeftStatement.lean) holds
`K3Left … g rs` of what s has heard; two of that structure's fields are: cEndEnts : g.cEnd.ents =
  #[]; shape : g.shape = h.

  `leftOn_cEnd`, `leftOn_shape`: the two projections, at whatever s has heard.
  `seen_look`: where the head's segment is opened, what the head's readers see as lookHeard is the
    state's `lookHeard?`.
  `hb_of_leftOn`: **the promise at the calls' seat at s; kap shows what the head's readers see ⊢ hb
    at fixed9 φ s.**
  `entsJoin_at_347'`: **the clause entsJoin at 347 with LC (that promise) in the place of hb.**
Limits. LC IS A PREMISE: it is what the table's item "leftOn" says; it is drawn from no promise
here. The other premises of `entsJoin_at_347` stay. No soundness statement.
-/
import Johnson.Desc.First.Link.Law.EntsHeadAt
import Johnson.Top.H.K3LeftStatement

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open OnBytes.Tie.Pv.Tail.Closed (shapesOf)
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.TailClaims.Law (blank)
open VerifiableInference.Desc.Kinds.Head
open VerifiableInference.Desc.Kinds.Head.Law
open VerifiableInference.OnPublicFiles (K3LeftOn)
open Johnson.Desc.First.Walk.Tied (RchAt)
open ProofFile (Cl)

/-- The form left for the join names no entry. -/
theorem leftOn_cEnd {T : Type} {fork : T → Option Fork} {heard : T → Option Forest.Heard}
    {h : Forest.Shape} {lm first : ℕ} {Qf : Fork → Prop} {s : T}
    (L : K3LeftOn fork heard h lm first Qf s) : ∀ g, heard s = some g → g.cEnd.ents = #[] := by
  obtain ⟨_, _, _, g0, _, _, _, K, hg, _⟩ := L
  intro g e
  obtain rfl : g0 = g := Option.some.inj (hg.symm.trans e)
  exact K.cEndEnts

/-- What was heard has the place's own shape. -/
theorem leftOn_shape {T : Type} {fork : T → Option Fork} {heard : T → Option Forest.Heard}
    {h : Forest.Shape} {lm first : ℕ} {Qf : Fork → Prop} {s : T}
    (L : K3LeftOn fork heard h lm first Qf s) : ∀ g, heard s = some g → g.shape = h := by
  obtain ⟨_, _, _, g0, _, _, _, K, hg, _⟩ := L
  intro g e
  obtain rfl : g0 = g := Option.some.inj (hg.symm.trans e)
  exact K.shape

/-- Where a ledger is open at the head's segment, the readers see the state's own. -/
theorem seen_look {s : S} {y : Seen} (h : seenOf s = some y) {G : Fork} (hG : s.fork? = some G) :
    y.lookHeard = s.lookHeard? := by
  unfold seenOf at h
  unfold S.lookHeard?
  unfold S.fork? at hG
  split at h
  · rename_i o ho
    obtain rfl := Option.some.inj h
    rw [ho] at hG ⊢
    by_cases hop : o.opened = true
    · simp [hop]
    · simp [hop] at hG
  · exact nomatch h

/-- **hb.** -/
theorem hb_of_leftOn {α : Type} (φ : S → α) (kap : α → Option Seen)
    (hkap : ∀ e, kap (φ e) = seenOf e) {hC : Forest.Shape} {lmC jC : ℕ} {QC : Fork → Prop} {s : S}
    (LC : K3LeftOn S.fork? S.lookHeard? hC lmC jC QC s) :
    ∀ y g, kap (fixed9 φ s).1 = some y → y.lookHeard = some g → g.cEnd.ents = #[] := by
  intro y g hy hg
  have hy' : seenOf s = some y := (hkap s).symm.trans hy
  obtain ⟨_, _, G, _, _, _, _, _, _, hG, _⟩ := id LC
  exact leftOn_cEnd LC g ((seen_look hy' hG).symm.trans hg)

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
  {α : Type} (π : α → Option HTailF2 × Option (Array HFun)) (φ : S → α) (u : HTailF2)
  (hh : OnBytes.Model.Head.Shape) (iU3 : ℕ) (p6 : Par) (kap : α → Option Seen)

/-- **THE CLAUSE entsJoin AT 347, FROM THE LOOKUPS' PROMISE AT THE CALLS' SEAT.** -/
theorem entsJoin_at_347' (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hi : Bs.G₀.W.H.tl.ix.U.getD 2 none = some iU3) {Xl : LinkH}
    (e3 : Bs.G₀.built[24]? = some Xl)
    (H : ∀ t0, tabsOfPlan Bs.G₀.W.hS Bs.G₀.W.H = some t0 →
      PosPlan Xl.tl Xl.Fp (shapesOf t0.funs))
    {Str : Type} (x : (ProofFile.InstPub × S) × Str)
    (h : RchAt (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s)
      (ProofFile.startS Z) c) 347 x)
    (hπ : ∀ s, π (φ s) = (s.tl?.map (blank u), s.funs?)) (hkap : ∀ e, kap (φ e) = seenOf e)
    {nU : Array ℕ} (h0 : 0 < nU.getD 2 0)
    (hthere : ((π (fixed9 φ x.1.2).1).1).isSome = true)
    (hs : ∀ tlb v, (π (fixed9 φ x.1.2).1).1 = some tlb → (fixed9 φ x.1.2).2 = some v →
      StaticOk tlb v.F)
    (hok : p6.ok = true) (hsz : p6.sizes = sizesOf hh)
    (hk : ∀ y w, kap (fixed9 φ x.1.2).1 = some y → (fixed9 φ x.1.2).2 = some w →
      K6Ready hh iU3 p6 y w.F)
    {hC : Forest.Shape} {lmC jC : ℕ} {QC : Fork → Prop}
    (LC : K3LeftOn S.fork? S.lookHeard? hC lmC jC QC x.1.2) :
    ∀ l, fsJoin hh iU3 p6 kap (fixed9 φ x.1.2) = some l → EntsAt π nU (fixed9 φ x.1.2) l :=
  entsJoin_at_347 π φ u hh iU3 p6 kap hS hR O hi e3 H x h hπ hkap h0 hthere hs hok hsz hk
    (hb_of_leftOn φ kap hkap LC)

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.leftOn_cEnd
#print axioms VerifiableInference.Desc.LinkJoin.leftOn_shape
#print axioms VerifiableInference.Desc.LinkJoin.seen_look
#print axioms VerifiableInference.Desc.LinkJoin.hb_of_leftOn
#print axioms VerifiableInference.Desc.LinkJoin.entsJoin_at_347'
