-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/EqBehind.lean: what the step "behind the batching" (`Link.runBehind`,
Johnson/Desc/Block.lean) does to the verifier's state, at each of the 25 segments of the first chain: said once, from
a yes of that step, for whoever needs a fact at the state in front of the sub-protocol "the one equation", which
stands right behind it.

The step runs "K8.lsTail", at a feed-forward segment "free-slot", and "K8.tests". The first writes one field of the
smallness test's record; the second hands the ledger back; the third lays the weights of the virtual rows on the rows of
their arrays (`coefBody`, Johnson/Desc/First/TailClaims/Coefficients.lean), which turns the ledger's field trees alone.

  `ButTrees F G`          two ledgers that differ at most in the field trees; `butTrees_coefBody`
  `rests_link`            the segment's book-keeping (`S.link?`) rests under the four writings of
                          Johnson/Desc/First/Link/Law/KeepsAny.lean
  **`behind_at_link`**     at a link with the library's `K8At` (Johnson/TocK8R/AtSeat.lean): from a yes of the step, from
                          sB to sE: every reading f that rests under the four writings, and that the runs between the
                          two named ones keep, reads the same at sE as at sB; sB has a ledger F and a record tl, something
                          g was heard; sE has the record tl with the one field written, and the ledger `coefBody` of F
  **`behind_scope`**       so at each l < 25, in the goals' scope, at an opening; **`behind_at_head`**: under `AtMgA`

The proofs follow Johnson/AtFull/Shape/RowFormSeat.lean's `termsV_at_link` and `termsV_scope`.

Limits. Implications from a yes of the step: that it returns at any state is not proved here. The hash function `secondHashFunction`
alone. This file proves no property of a prover or a protocol.
-/
import Johnson.AtFull.Shape.RowFormSeat
import Johnson.Desc.First.Link.Law.KeepsAny
import Johnson.Desc.First.TailClaims.EquationsTested
import Johnson.Desc.First.TailClaims.EquationsTests
import Johnson.P5J.MgAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K9
open Inst.Model
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName Claim claimsInBy afterIn)
open VerifiableInference.Desc.First (S ModelPart kindsBeforeBatching orderOf orderAfterOf)
open VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.TailClaims.Law
open VerifiableInference.Desc.LinkJoin (FieldRests)
open Johnson.AtFull.Shape (LeavesLedger)
open ProofFile (Cl)
open IM
open TocK8 (K8At afterIn_of_behind k08_scope ixOf preOf postOf midOf)

/-- Two ledgers that differ at most in the field trees. -/
def ButTrees (F G : Fork) : Prop := { G with trees := F.trees } = F

theorem ButTrees.refl (F : Fork) : ButTrees F F := rfl

/-- The step that lays the virtual rows' weights turns the field trees alone. -/
theorem butTrees_coefBody (tl : HTailF2) (g : Forest.Heard) (F : Fork) : ButTrees F (coefBody tl g F) :=
  coefBody_inv (fun G => ButTrees F G) (fun _ _ _ _ h => h) tl g F rfl

/-- The segment's book-keeping rests under the four writings. -/
theorem rests_link : FieldRests S.link? where
  tl s tl := by
    unfold S.link? S.putTl
    cases h : s.here with
    | head a => by_cases ho : a.opened = true <;> simp [h, ho]
    | _ => simp [h]
  fork s G := by
    unfold S.link? S.putFork
    cases h : s.here with
    | head a => by_cases ho : a.opened = true <;> simp [h, ho]
    | _ => simp [h]
  wrote e _ _ _ hw := by
    obtain ⟨h1, rfl⟩ := hw
    unfold S.link?
    simp [h1]
  head s a G h := by
    unfold S.link?
    simp [h]

/-- **At a link with the library's `K8At`.** -/
theorem behind_at_link {Lk : Link S Cl} {p : VerifiableInference.Desc.First.K8.ParW} {i : ℕ}
    {pre post mid : List (ℕ × String)} (K : K8At Lk p i pre post mid)
    (hF : ∀ o ∈ mid, LeavesLedger Lk.hear o) {γ : Type} (f : S → γ) (R : FieldRests f)
    (hf : ∀ o ∈ mid, ∀ run, ((Lk.hear[o.1]?).bind fun b => b.after.lookup o.2) = some run →
      ∀ e e₁, run e = .ok e₁ → f e₁ = f e)
    (sB sE : S) (h2 : Lk.runBehind sB = .ok sE) :
    f sE = f sB ∧ ∃ F tl g, sB.fork? = some F ∧ sB.tl? = some tl ∧ tl.heard = some g ∧
      sE.tl? = some { tl with lsTail := F.LS.extract tl.slotA tl.slotB } ∧
      sE.fork? = some (coefBody { tl with lsTail := F.LS.extract tl.slotA tl.slotB } g F) := by
  have fset : ∀ (s : S) (q : K8Part), f (k8PartP.set s q) = f s := fun s q => by
    have e : k8PartP.set s q = (s.putTl q.tl).putFork q.F := rfl
    rw [e, R.fork, R.tl]
  have ha := afterIn_of_behind h2
  rw [K.after] at ha
  obtain ⟨rL', s₁, hlL, hrL, ha'⟩ := afterIn_cons ha
  obtain ⟨s₂, -, hkeep, ha''⟩ :=
    afterIn_keeps (fun s : S => ((k8Field s, s.fork?), f s)) mid [(i, "K8.tests")] s₁ sE
      (fun o ho run hl e e₁ hr =>
        Prod.ext (Prod.ext (K.hmid o ho run hl e e₁ hr) (hF o ho run hl e e₁ hr)) (hf o ho run hl e e₁ hr)) ha'
  obtain ⟨rT', s₃, hlT, hrT, hend⟩ := afterIn_cons ha''
  obtain rfl : s₃ = sE := Except.ok.inj hend
  obtain ⟨rL, mL, uL⟩ := K.hL rL' hlL
  obtain ⟨rT, mT, uT⟩ := K.hT rT' hlT
  obtain ⟨q, hq, rfl⟩ := (sits_lsTail p rL mL sB s₁).1 (uL _ _ hrL)
  obtain ⟨q₂, Fc, hq₂, ht, rfl⟩ := (sits_tests p rT mT s₂ _).1 (uT _ _ hrT)
  obtain ⟨b1, b2, -⟩ := partOf_some.1 hq
  obtain ⟨c1, c2, -⟩ := partOf_some.1 (part_set hq
    { q with tl := { q.tl with lsTail := q.F.LS.extract q.tl.slotA q.tl.slotB } })
  obtain ⟨d1, d2, -⟩ := partOf_some.1 hq₂
  obtain ⟨k0, kf⟩ := Prod.mk.inj hkeep
  obtain ⟨k1, k2⟩ := Prod.mk.inj k0
  have k3 := (Prod.mk.inj k1).1
  have e1 : q₂.tl = { q.tl with lsTail := q.F.LS.extract q.tl.slotA q.tl.slotB } :=
    Option.some.inj (d1.symm.trans (k3.trans c1))
  have e2 : q₂.F = q.F := Option.some.inj (d2.symm.trans (k2.trans c2))
  obtain ⟨g1, g2, -⟩ := partOf_some.1 (part_set hq₂ { q₂ with F := Fc })
  rw [e1, e2] at ht
  obtain ⟨-, hc, -⟩ := tests_ok ht
  unfold coefficientsP at hc
  split at hc
  · exact nomatch hc
  · rename_i g hg
    obtain rfl := Except.ok.inj hc
    refine ⟨?_, q.F, q.tl, g, b2, b1, hg, ?_, g2⟩
    · rw [fset, kf, fset]
    · rw [g1]
      exact congrArg some e1

/-- **At each of the 25 segments, in the goals' scope, at an opening.** -/
theorem behind_scope {P : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
    {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
    {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (l : ℕ) (hl : l < 25) (Lk : Link S Cl)
    (hLk : c.links[l]? = some Lk) {γ : Type} (f : S → γ) (R : FieldRests f) (sB sE : S)
    (h2 : Lk.runBehind sB = .ok sE) :
    f sE = f sB ∧ ∃ F tl g, sB.fork? = some F ∧ sB.tl? = some tl ∧ tl.heard = some g ∧
      sE.tl? = some { tl with lsTail := F.LS.extract tl.slotA tl.slotB } ∧
      sE.fork? = some (coefBody { tl with lsTail := F.LS.extract tl.slotA tl.slotB } g F) := by
  obtain ⟨Lk', Xl, e, -, K, -⟩ := k08_scope hS hR O l hl
  obtain rfl : Lk' = Lk := Option.some.inj (e.symm.trans hLk)
  have key : ∀ o ∈ midOf (subAt l), ∀ run, ((Lk'.hear[o.1]?).bind fun b => b.after.lookup o.2) = some run →
      ∀ e e₁, run e = .ok e₁ → e₁.fork? = e.fork? ∧ f e₁ = f e := by
    intro o ho run hlk e₀ e₁ hr
    by_cases h24 : l = 24
    · subst h24
      exact nomatch ho
    · by_cases he : l % 2 = 0
      · have ej : 2 * (l / 2) = l := by omega
        have hs : subAt l = .layers := by
          rw [← ej]
          exact subAt_layers (l / 2) (by omega)
        rw [hs] at ho
        obtain rfl := List.mem_singleton.1 ho
        obtain ⟨L4, b4, x, e4, hb4, -, la4, -⟩ := k4_of hS hR O (l / 2) (by omega)
        rw [ej] at e4
        obtain rfl : Lk' = L4 := Option.some.inj (e.symm.trans e4)
        rw [show ((2, "free-slot") : ℕ × String).1 = 2 from rfl, hb4] at hlk
        obtain ⟨r', hl', -, hy⟩ := after_yes la4 hlk
        refine ⟨(freeSlot_field (p := { x.2 with k3Runs := true }) hl' ((hy e₀ e₁).1 hr).1).2, ?_⟩
        obtain ⟨a, hw⟩ := OnBytes.Desc.First.K4.freeSlotAtS (p := { x.2 with k3Runs := true })
          (show (OnBytes.Desc.First.K4.blockAtS { x.2 with k3Runs := true }).after.lookup "free-slot" = some r'
            from hl') ((hy e₀ e₁).1 hr).1
        exact R.wrote _ _ _ _ hw
      · have ej : 2 * (l / 2) + 1 = l := by omega
        have hs : subAt l = .attention := by
          rw [← ej]
          exact subAt_attention (l / 2)
        rw [hs] at ho
        exact nomatch ho
  exact behind_at_link K (fun o ho run hlk e₀ e₁ hr => (key o ho run hlk e₀ e₁ hr).1) f R
    (fun o ho run hlk e₀ e₁ hr => (key o ho run hlk e₀ e₁ hr).2) sB sE h2

/-- **Under the library's hypothesis.** -/
theorem behind_at_head {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
    (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : ℕ) (hl : l < 25) (Lk : Link S Cl)
    (hLk : cF.links[l]? = some Lk) {γ : Type} (f : S → γ) (R : FieldRests f) (sB sE : S)
    (h2 : Lk.runBehind sB = .ok sE) :
    f sE = f sB ∧ ∃ F tl g, sB.fork? = some F ∧ sB.tl? = some tl ∧ tl.heard = some g ∧
      sE.tl? = some { tl with lsTail := F.LS.extract tl.slotA tl.slotB } ∧
      sE.fork? = some (coefBody { tl with lsTail := F.LS.extract tl.slotA tl.slotB } g F) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  exact behind_scope h.scope h.reads O l hl Lk hLk f R sB sE h2

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.butTrees_coefBody
#print axioms ProofFile.Honest.K9.rests_link
#print axioms ProofFile.Honest.K9.behind_at_link
#print axioms ProofFile.Honest.K9.behind_scope
#print axioms ProofFile.Honest.K9.behind_at_head
