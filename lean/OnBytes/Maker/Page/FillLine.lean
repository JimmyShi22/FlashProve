-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/Page/FillLine.lean: the data of a file's page at the rounds of a whole file
(OnBytes/Maker/Page/Fill.lean, `fillJ`) fit the file's three stretches in the sense of
OnBytes/Maker/Page/Chains.lean (`FitsEnd`, `FitsShE`), at the embeddings of
OnBytes/TypedOracleCompiler/Joined/K/RunsLine.lean (`embL₁`, `embL₂`, `embL₃`).

Two hypotheses. The read-back `rd` undoes the verifier's embedding `embP` of the file's plain parts
into the interface's. And the condition `Q` on chain queries, a letter of Chains.lean, holds of
every query with the stretch's form of head that bears a plain part of the stretch as embedded,
whatever its round, chain value and roots.

  `pTo_inl`, `pTo_inr`: a plain part carried along an equation of annotations, at a first round and
    behind it.
  `roundFits_of`: one round: from what `partAt` gives at its plain parts as embedded, its data, and
    the condition `Q` at its queries.
  `fitsEnd_of`, `fitsShE_of`: by induction along a stretch: from what `partAt` gives at the embedded
    plain parts, the rounds' data at the typed rounds, and the condition `Q` at the stretch's
    queries.
  `fitsEnd₁`, `fitsShE₂`, `fitsEnd₃`: the three stretches of a file.
  `e₁`, `e₂`, `e₃`: these three embeddings at the rounds of `chainsOf C D tF tJ t3`.
  `partAt_front`, `partAt_join`, `partAt_seam`: at the three silent rounds' messages as embedded.
  `partAt_one`, `partAt_two`, `partAt_three`: at a plain part of a stretch as embedded.
  `one_ne_front`, `two_ne_front`, `three_ne_front`: a written round's plain part as embedded is not
    the front round's as embedded: nobody calls these three. `ofSaid_ne_front`: a tool.

What is not claimed. That a read-back with that law exists at any interface.


-/
import OnBytes.Maker.Page.FillLaws
import OnBytes.Maker.Page.Chains
import OnBytes.Maker.LineAt

set_option autoImplicit false

namespace OnBytes.Maker.Page

open TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Joined TypedOracleCompiler.Joined.K Rom
open _root_.Compile hiding ON
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ _root_.Compile.Joined
open _root_.Run.Twin (allLo allLo_eq)

theorem pTo_inl {r : Round} {s : Shape} (a : RAnn r) {A A' : RoundSplits s} (h : A = A')
    (h' : ((a, A) : RoundSplits (r :: s)) = (a, A')) (x : a.P0 ⊕ a.Pj) :
    pTo (s := r :: s) (A := (a, A)) (A' := (a, A')) h' (Sum.inl x) = Sum.inl x := by
  subst h
  rfl

theorem pTo_inr {r : Round} {s : Shape} (a : RAnn r) {A A' : RoundSplits s} (h : A = A')
    (h' : ((a, A) : RoundSplits (r :: s)) = (a, A')) (z : PlainPart s A) :
    pTo (s := r :: s) (A := (a, A)) (A' := (a, A')) h' (Sum.inr z) = Sum.inr (pTo h z) := by
  subst h
  rfl

/-- What `PartJ.ofSaid` gives is not the front round's message. -/
theorem ofSaid_ne_front {TF TJ T3 : Type} (a : ℕ) (s : Option Said) (p : TF) :
    (PartJ.ofSaid a s : PartJ TF TJ T3) ≠ .front p := by
  cases s <;> exact fun h => nomatch h

section
variable {I X : Type} {L : BatchProtocolWithLeafBody I X} {t : Tag} (C : CK) (D : WholeD) {TF TJ T3 : Type} (tF : TF)
  (tJ : TJ) (t3 : T3)
  (rd : PBt L t → Option (PlainPart (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann))
  (S : SilentJ X TF TJ T3) (Q : FbIn 256 L t → Prop)

/-- One round, from what `partAt` gives at its plain parts as embedded and the round's data. -/
theorem roundFits_of (hd : Bits → Head 256 X) (d : RDT) (e : (roundT C d).Plain → PBt L t) (i : ℕ)
    (hQ : ∀ ρ rt pl, Q ⟨i, hd ρ, rt, e pl⟩)
    (hP : ∀ pl, partAt C D tF tJ t3 rd (e pl) =
      .row i (saidOf C d pl).msg (saidOf C d pl).nonce)
    (hR : rdAt D i = some d) : RoundFitsJ (fillJ C D tF tJ t3 rd S) Q C hd d.toRD e i where
  ours := hQ
  kind := kindAt_of D hR
  work := workAt_of D hR
  msg := fun bs pl => by
    show (match partAt C D tF tJ t3 rd (e pl) with
      | .row i' m _ => if i' = i then m bs else ByteArray.empty
      | _ => ByteArray.empty) = _
    rw [hP pl]
    exact if_pos rfl
  nonce := fun pl => by
    show (match partAt C D tF tJ t3 rd (e pl) with
      | .row i' _ n => if i' = i then n else 0
      | _ => 0) = _
    rw [hP pl]
    exact if_pos rfl

/-- **Along a stretch of local rounds.** -/
theorem fitsEnd_of : ∀ (ds : List RDT) (a : ℕ)
    (e : PlainPart (TypedOracleCompiler.Run.PQ.uL C (toRDs ds)) (allLo (TypedOracleCompiler.Run.PQ.SL C (toRDs ds))) → PBt L t),
    (∀ i ρ rt z, Q ⟨i, .f2 none ρ, rt, e z⟩) →
    (∀ z, partAt C D tF tJ t3 rd (e z) =
      PartJ.ofSaid a (saidLo C ds (pTo (allLo_eq (TypedOracleCompiler.Run.PQ.SL C (toRDs ds))) z))) →
    (∀ k, k < ds.length → rdAt D (a + 1 + k) = ds[k]?) →
    FitsEnd (fillJ C D tF tJ t3 rd S) Q C (toRDs ds) e (a + 1)
  | [], _, _, _, _, _ => trivial
  | d :: ds, a, e, hQ, hP, hR => by
    refine ⟨roundFits_of C D tF tJ t3 rd S Q _ d _ (a + 1) (fun ρ rt pl => hQ _ ρ rt _)
        (fun pl => ?_) ?_,
      fitsEnd_of ds (a + 1) (fun z => e (.inr z)) (fun i ρ rt z => hQ i ρ rt _) (fun z => ?_)
        fun k hk => ?_⟩
    · rw [hP]
      exact congrArg (fun w => PartJ.ofSaid a (saidLo C (d :: ds) w))
        (pTo_inl (RAnn.allLocal (roundT C d).up) (allLo_eq (TypedOracleCompiler.Run.PQ.SL C (toRDs ds)))
          (allLo_eq (TypedOracleCompiler.Run.PQ.SL C (toRDs (d :: ds)))) (.inr pl))
    · exact hR 0 (Nat.succ_pos _)
    · rw [hP]
      exact (congrArg (fun w => PartJ.ofSaid a (saidLo C (d :: ds) w))
        (pTo_inr (RAnn.allLocal (roundT C d).up) (allLo_eq (TypedOracleCompiler.Run.PQ.SL C (toRDs ds)))
          (allLo_eq (TypedOracleCompiler.Run.PQ.SL C (toRDs (d :: ds)))) z)).trans (ofSaid_next a _)
    · have h := hR (k + 1) (Nat.succ_lt_succ hk)
      rw [show a + 1 + (k + 1) = a + 1 + 1 + k by omega] at h
      exact h

/-- **Along a stretch of shared rounds.** -/
theorem fitsShE_of : ∀ (ds : List RDT) (a : ℕ)
    (e : PlainPart (TypedOracleCompiler.Run.PQ.uL C (toRDs ds)) (TypedOracleCompiler.Run.PQ.annShE C (toRDs ds)) → PBt L t),
    (∀ i ρ rt z, Q ⟨i, .f5 ρ, rt, e z⟩) →
    (∀ z, partAt C D tF tJ t3 rd (e z) =
      PartJ.ofSaid a (saidSh C ds (pTo (TypedOracleCompiler.Run.PQ.annShE_eq C (toRDs ds)) z))) →
    (∀ k, k < ds.length → rdAt D (a + 1 + k) = ds[k]?) →
    FitsShE (fillJ C D tF tJ t3 rd S) Q C (toRDs ds) e (a + 1)
  | [], _, _, _, _, _ => trivial
  | d :: ds, a, e, hQ, hP, hR => by
    refine ⟨roundFits_of C D tF tJ t3 rd S Q _ d _ (a + 1) (fun ρ rt pl => hQ _ ρ rt _)
        (fun pl => ?_) ?_,
      fitsShE_of ds (a + 1) (fun z => e (.inr z)) (fun i ρ rt z => hQ i ρ rt _) (fun z => ?_)
        fun k hk => ?_⟩
    · rw [hP]
      exact congrArg (fun w => PartJ.ofSaid a (saidSh C (d :: ds) w))
        (pTo_inl (RAnn.ofShared .sh (roundT C d).up) (TypedOracleCompiler.Run.PQ.annShE_eq C (toRDs ds))
          (TypedOracleCompiler.Run.PQ.annShE_eq C (toRDs (d :: ds))) (.inl pl))
    · exact hR 0 (Nat.succ_pos _)
    · rw [hP]
      exact (congrArg (fun w => PartJ.ofSaid a (saidSh C (d :: ds) w))
        (pTo_inr (RAnn.ofShared .sh (roundT C d).up) (TypedOracleCompiler.Run.PQ.annShE_eq C (toRDs ds))
          (TypedOracleCompiler.Run.PQ.annShE_eq C (toRDs (d :: ds))) z)).trans (ofSaid_next a _)
    · have h := hR (k + 1) (Nat.succ_lt_succ hk)
      rw [show a + 1 + (k + 1) = a + 1 + 1 + k by omega] at h
      exact h

/-! ## The three stretches and the three silent rounds of a file -/

variable (embP : PlainPart (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann → PBt L t)
  (hrd : ∀ w, rd (embP w) = some w)

/-- The first chain's embedding of OnBytes/TypedOracleCompiler/Joined/K/RunsLine.lean, at the rounds of
`chainsOf C D tF tJ t3`. -/
abbrev e₁ : PlainPart (Twin.up (plainRS TF tF :: SLT C D.ds₁))
    ((plainRS TF tF).lo, allLo (SLT C D.ds₁)) → PBt L t :=
  embL₁ (C := C) (rF := plainRS TF tF) (rJ := plainRS TJ tJ) (r3 := plainRS T3 t3)
    (aJ := RAnn.ofShared .sh _) (ds₁ := toRDs D.ds₁) (ds₂ := toRDs D.ds₂) (ds₃ := toRDs D.ds₃) embP

/-- The second chain's. -/
abbrev e₂ : PlainPart (Twin.up (plainRS TJ tJ :: SLT C D.ds₂))
    (annW₂ C (plainRS TJ tJ) (RAnn.ofShared .sh _) (toRDs D.ds₂)) → PBt L t :=
  embL₂ (C := C) (rF := plainRS TF tF) (rJ := plainRS TJ tJ) (r3 := plainRS T3 t3)
    (aJ := RAnn.ofShared .sh _) (ds₁ := toRDs D.ds₁) (ds₂ := toRDs D.ds₂) (ds₃ := toRDs D.ds₃) embP

/-- The third chain's. -/
abbrev e₃ : PlainPart (Twin.up (plainRS T3 t3 :: SLT C D.ds₃))
    ((plainRS T3 t3).lo, allLo (SLT C D.ds₃)) → PBt L t :=
  embL₃ (C := C) (rF := plainRS TF tF) (rJ := plainRS TJ tJ) (r3 := plainRS T3 t3)
    (aJ := RAnn.ofShared .sh _) (ds₁ := toRDs D.ds₁) (ds₂ := toRDs D.ds₂) (ds₃ := toRDs D.ds₃) embP

include hrd

theorem partAt_front (p : TF) :
    partAt C D tF tJ t3 rd (e₁ C D tF tJ t3 embP (Sum.inl (Sum.inr p))) = .front p := by
  show partAt C D tF tJ t3 rd (embP (in₁ C D tF tJ t3
    (pTo (allLo_eq (plainRS TF tF :: SLT C D.ds₁)) (Sum.inl (Sum.inr p))))) = _
  unfold partAt
  rw [hrd]
  exact (congrArg (fun w => partOf C D tF tJ t3 (in₁ C D tF tJ t3 w))
    (pTo_inl (RAnn.allLocal (plainRound TF tF)) (allLo_eq (SLT C D.ds₁))
      (allLo_eq (plainRS TF tF :: SLT C D.ds₁)) (Sum.inr p))).trans (partOf_front C D tF tJ t3 p)

theorem partAt_one (z : PlainPart (TypedOracleCompiler.Run.PQ.uL C (toRDs D.ds₁)) (allLo (SLT C D.ds₁))) :
    partAt C D tF tJ t3 rd (e₁ C D tF tJ t3 embP (Sum.inr z)) =
      PartJ.ofSaid 0 (saidLo C D.ds₁ (pTo (allLo_eq (SLT C D.ds₁)) z)) := by
  show partAt C D tF tJ t3 rd (embP (in₁ C D tF tJ t3
    (pTo (allLo_eq (plainRS TF tF :: SLT C D.ds₁)) (Sum.inr z)))) = _
  unfold partAt
  rw [hrd]
  exact (congrArg (fun w => partOf C D tF tJ t3 (in₁ C D tF tJ t3 w))
    (pTo_inr (RAnn.allLocal (plainRound TF tF)) (allLo_eq (SLT C D.ds₁))
      (allLo_eq (plainRS TF tF :: SLT C D.ds₁)) z)).trans (partOf_one C D tF tJ t3 _)

theorem partAt_join (p : TJ) :
    partAt C D tF tJ t3 rd (e₂ C D tF tJ t3 embP (Sum.inl (Sum.inl p))) = .join p := by
  show partAt C D tF tJ t3 rd (embP (in₂ C D tF tJ t3
    (pTo (annL₂ C (plainRS TF tF) (plainRS TJ tJ) (plainRS T3 t3) (RAnn.ofShared .sh _)
      (toRDs D.ds₁) (toRDs D.ds₂) (toRDs D.ds₃)) (Sum.inl (Sum.inl p))))) = _
  unfold partAt
  rw [hrd]
  exact (congrArg (fun w => partOf C D tF tJ t3 (in₂ C D tF tJ t3 w))
    (pTo_inl (RAnn.ofShared .sh (plainRound TJ tJ)) (TypedOracleCompiler.Run.PQ.annShE_eq C (toRDs D.ds₂))
      (annL₂ C (plainRS TF tF) (plainRS TJ tJ) (plainRS T3 t3) (RAnn.ofShared .sh _)
        (toRDs D.ds₁) (toRDs D.ds₂) (toRDs D.ds₃)) (Sum.inl p))).trans (partOf_join C D tF tJ t3 p)

theorem partAt_two (z : PlainPart (TypedOracleCompiler.Run.PQ.uL C (toRDs D.ds₂)) (TypedOracleCompiler.Run.PQ.annShE C (toRDs D.ds₂))) :
    partAt C D tF tJ t3 rd (e₂ C D tF tJ t3 embP (Sum.inr z)) =
      PartJ.ofSaid (D.ds₁.length + 1)
        (saidSh C D.ds₂ (pTo (TypedOracleCompiler.Run.PQ.annShE_eq C (toRDs D.ds₂)) z)) := by
  show partAt C D tF tJ t3 rd (embP (in₂ C D tF tJ t3
    (pTo (annL₂ C (plainRS TF tF) (plainRS TJ tJ) (plainRS T3 t3) (RAnn.ofShared .sh _)
      (toRDs D.ds₁) (toRDs D.ds₂) (toRDs D.ds₃)) (Sum.inr z)))) = _
  unfold partAt
  rw [hrd]
  exact (congrArg (fun w => partOf C D tF tJ t3 (in₂ C D tF tJ t3 w))
    (pTo_inr (RAnn.ofShared .sh (plainRound TJ tJ)) (TypedOracleCompiler.Run.PQ.annShE_eq C (toRDs D.ds₂))
      (annL₂ C (plainRS TF tF) (plainRS TJ tJ) (plainRS T3 t3) (RAnn.ofShared .sh _)
        (toRDs D.ds₁) (toRDs D.ds₂) (toRDs D.ds₃)) z)).trans (partOf_two C D tF tJ t3 _)

theorem partAt_seam (p : T3) :
    partAt C D tF tJ t3 rd (e₃ C D tF tJ t3 embP (Sum.inl (Sum.inr p))) = .seam p := by
  show partAt C D tF tJ t3 rd (embP (in₃ C D tF tJ t3
    (pTo (allLo_eq (plainRS T3 t3 :: SLT C D.ds₃)) (Sum.inl (Sum.inr p))))) = _
  unfold partAt
  rw [hrd]
  exact (congrArg (fun w => partOf C D tF tJ t3 (in₃ C D tF tJ t3 w))
    (pTo_inl (RAnn.allLocal (plainRound T3 t3)) (allLo_eq (SLT C D.ds₃))
      (allLo_eq (plainRS T3 t3 :: SLT C D.ds₃)) (Sum.inr p))).trans (partOf_seam C D tF tJ t3 p)

theorem partAt_three (z : PlainPart (TypedOracleCompiler.Run.PQ.uL C (toRDs D.ds₃)) (allLo (SLT C D.ds₃))) :
    partAt C D tF tJ t3 rd (e₃ C D tF tJ t3 embP (Sum.inr z)) =
      PartJ.ofSaid (D.ds₁.length + D.ds₂.length + 2)
        (saidLo C D.ds₃ (pTo (allLo_eq (SLT C D.ds₃)) z)) := by
  show partAt C D tF tJ t3 rd (embP (in₃ C D tF tJ t3
    (pTo (allLo_eq (plainRS T3 t3 :: SLT C D.ds₃)) (Sum.inr z)))) = _
  unfold partAt
  rw [hrd]
  exact (congrArg (fun w => partOf C D tF tJ t3 (in₃ C D tF tJ t3 w))
    (pTo_inr (RAnn.allLocal (plainRound T3 t3)) (allLo_eq (SLT C D.ds₃))
      (allLo_eq (plainRS T3 t3 :: SLT C D.ds₃)) z)).trans (partOf_three C D tF tJ t3 _)

/-- **A written round's plain part as embedded is not the front round's as embedded**: first
chain. -/
theorem one_ne_front (z : PlainPart (TypedOracleCompiler.Run.PQ.uL C (toRDs D.ds₁)) (allLo (SLT C D.ds₁))) (p : TF) :
    e₁ C D tF tJ t3 embP (Sum.inr z) ≠ e₁ C D tF tJ t3 embP (Sum.inl (Sum.inr p)) := fun h =>
  ofSaid_ne_front _ _ p ((partAt_one C D tF tJ t3 rd embP hrd z).symm.trans
    ((congrArg (partAt C D tF tJ t3 rd) h).trans (partAt_front C D tF tJ t3 rd embP hrd p)))

/-- Second chain. -/
theorem two_ne_front
    (z : PlainPart (TypedOracleCompiler.Run.PQ.uL C (toRDs D.ds₂)) (TypedOracleCompiler.Run.PQ.annShE C (toRDs D.ds₂))) (p : TF) :
    e₂ C D tF tJ t3 embP (Sum.inr z) ≠ e₁ C D tF tJ t3 embP (Sum.inl (Sum.inr p)) := fun h =>
  ofSaid_ne_front _ _ p ((partAt_two C D tF tJ t3 rd embP hrd z).symm.trans
    ((congrArg (partAt C D tF tJ t3 rd) h).trans (partAt_front C D tF tJ t3 rd embP hrd p)))

/-- Third chain. -/
theorem three_ne_front (z : PlainPart (TypedOracleCompiler.Run.PQ.uL C (toRDs D.ds₃)) (allLo (SLT C D.ds₃))) (p : TF) :
    e₃ C D tF tJ t3 embP (Sum.inr z) ≠ e₁ C D tF tJ t3 embP (Sum.inl (Sum.inr p)) := fun h =>
  ofSaid_ne_front _ _ p ((partAt_three C D tF tJ t3 rd embP hrd z).symm.trans
    ((congrArg (partAt C D tF tJ t3 rd) h).trans (partAt_front C D tF tJ t3 rd embP hrd p)))

/-- **The data fit the first chain's rounds.** -/
theorem fitsEnd₁ (hQ : ∀ i ρ rt z, Q ⟨i, .f2 none ρ, rt, e₁ C D tF tJ t3 embP (Sum.inr z)⟩) :
    FitsEnd (fillJ C D tF tJ t3 rd S) Q C (toRDs D.ds₁)
      (fun z => e₁ C D tF tJ t3 embP (Sum.inr z)) (0 + 1) :=
  fitsEnd_of C D tF tJ t3 rd S Q D.ds₁ 0 _ hQ (partAt_one C D tF tJ t3 rd embP hrd)
    fun k hk => rdAt_one D k hk

/-- **The second chain's.** -/
theorem fitsShE₂ (hQ : ∀ i ρ rt z, Q ⟨i, .f5 ρ, rt, e₂ C D tF tJ t3 embP (Sum.inr z)⟩) :
    FitsShE (fillJ C D tF tJ t3 rd S) Q C (toRDs D.ds₂)
      (fun z => e₂ C D tF tJ t3 embP (Sum.inr z)) (D.ds₁.length + 1 + 1) :=
  fitsShE_of C D tF tJ t3 rd S Q D.ds₂ (D.ds₁.length + 1) _ hQ
    (partAt_two C D tF tJ t3 rd embP hrd) fun k hk => rdAt_two D k hk

/-- **The third chain's.** -/
theorem fitsEnd₃ (hQ : ∀ i ρ rt z, Q ⟨i, .f2 none ρ, rt, e₃ C D tF tJ t3 embP (Sum.inr z)⟩) :
    FitsEnd (fillJ C D tF tJ t3 rd S) Q C (toRDs D.ds₃)
      (fun z => e₃ C D tF tJ t3 embP (Sum.inr z)) (D.ds₁.length + D.ds₂.length + 2 + 1) :=
  fitsEnd_of C D tF tJ t3 rd S Q D.ds₃ (D.ds₁.length + D.ds₂.length + 2) _ hQ
    (partAt_three C D tF tJ t3 rd embP hrd) fun k _ => rdAt_three D k

end

end OnBytes.Maker.Page
