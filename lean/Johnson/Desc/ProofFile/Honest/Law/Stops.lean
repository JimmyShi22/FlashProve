-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Stops.lean: the abort set of `honestB` (Honest/Record.lean),
compared with the one silent set of Honest/Rule.lean. The abort set is the library's field
`withheld`, a set of verifier's messages. The main lemma, `withheld_iff`: where the request has a
trace, the abort set is the silent set (`silentAt`), read at `drawsAt`.

  1  `loTake_lo`, `loSkip_lo`, `shTake_sh`, `shSkip_sh`, `loEnd_lo`, `drawsLo_at`,
     `drawsSh_at`   what `honestB` reads of the local and of the shared verifier's messages is the
     three lists of `drawsAt`
  2  `StopRel` and its lemmas, `isSome_or`   whether a chain stops at what the second stops may
     read, compared with whether it stops with nothing supplied: a first stop is seen by both; with
     something supplied there is no other class than the two
  3  `withheld_reads`, `withheld_congr`   the abort set reads a verifier's message through `drawsAt`
     alone, at every private input and instance; `withheld_iff`: where the request has a trace, it
     is the one silent set, read at `drawsAt`

Limits.
  * Nothing is measured.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Record
import Johnson.Desc.ProofFile.Honest.Law.StratWords

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc
open OnBytes.Maker (RDT WholeD uLT roundT chainsOf drawnT)
open _root_.Run.PQ (CK SgX)

variable {Xi W₀ Rc Ky Tr X₀ X Sd TF TJ T3 R2 R3 S Cl V W Y : Type}

/-! ## 1 What `honestB` reads of the verifier's messages -/

section
variable (C : CK) {rest : Iop.Shape} (A : Iop.RoundSplits rest)

theorem loTake_lo : ∀ (ds : List RDT) (ρ : Iop.Rho (uLT C ds ++ rest)),
    loTake C ds (Iop.Rho.lo (Iop.RoundSplits.app (Iop.RoundSplits.allLocal (uLT C ds)) A) ρ) =
      (drawnT C ds (Iop.Rho.fst ρ), Iop.Rho.lo A (Iop.Rho.snd (s := uLT C ds) ρ))
  | [], _ => rfl
  | d :: ds, (c, ρ) => by
    have ih := loTake_lo ds ρ
    show ((drOf C d c :: (loTake C ds (Iop.Rho.lo (Iop.RoundSplits.app (Iop.RoundSplits.allLocal (uLT C ds)) A)
      ρ)).1), (loTake C ds (Iop.Rho.lo (Iop.RoundSplits.app (Iop.RoundSplits.allLocal (uLT C ds)) A) ρ)).2) = _
    rw [ih]
    rfl

theorem loSkip_lo : ∀ (ds : List RDT) (ρ : Iop.Rho (uLT C ds ++ rest)),
    loSkip C ds (Iop.Rho.lo (Iop.RoundSplits.app (Iop.RoundSplits.const (Iop.RAnn.ofShared .sh) (uLT C ds)) A)
      ρ) = Iop.Rho.lo A (Iop.Rho.snd (s := uLT C ds) ρ)
  | [], _ => rfl
  | _ :: ds, (_, ρ) => loSkip_lo ds ρ

theorem shTake_sh : ∀ (ds : List RDT) (ρ : Iop.Rho (uLT C ds ++ rest)),
    shTake C ds (Iop.Rho.sh (Iop.RoundSplits.app (Iop.RoundSplits.const (Iop.RAnn.ofShared .sh) (uLT C ds)) A)
      ρ) = (drawnT C ds (Iop.Rho.fst ρ), Iop.Rho.sh A (Iop.Rho.snd (s := uLT C ds) ρ))
  | [], _ => rfl
  | d :: ds, (c, ρ) => by
    have ih := shTake_sh ds ρ
    show ((drOf C d c :: (shTake C ds (Iop.Rho.sh (Iop.RoundSplits.app (Iop.RoundSplits.const
             (Iop.RAnn.ofShared .sh) (uLT C ds)) A) ρ)).1), (shTake C ds (Iop.Rho.sh (Iop.RoundSplits.app
               (Iop.RoundSplits.const (Iop.RAnn.ofShared .sh) (uLT C ds)) A) ρ)).2) = _
    rw [ih]
    rfl

theorem shSkip_sh : ∀ (ds : List RDT) (ρ : Iop.Rho (uLT C ds ++ rest)),
    shSkip C ds (Iop.Rho.sh (Iop.RoundSplits.app (Iop.RoundSplits.allLocal (uLT C ds)) A) ρ) =
      Iop.Rho.sh A (Iop.Rho.snd (s := uLT C ds) ρ)
  | [], _ => rfl
  | _ :: ds, (_, ρ) => shSkip_sh ds ρ

end

theorem loEnd_lo (C : CK) : ∀ (ds : List RDT) (ρ : Iop.Rho (uLT C ds)),
    loEnd C ds (Iop.Rho.lo (Iop.RoundSplits.allLocal (uLT C ds)) ρ) = drawnT C ds ρ
  | [], _ => rfl
  | d :: ds, (c, ρ) => congrArg (drOf C d c :: ·) (loEnd_lo C ds ρ)

section
variable (C : CK) (D : WholeD) (tF : TF) (tJ : TJ) (t3 : T3)

theorem drawsLo_at (ρ : Iop.Rho (chainsOf C D tF tJ t3).sh) :
    drawsLo C D tF tJ t3 (Iop.Rho.lo (chainsOf C D tF tJ t3).ann ρ) =
      ((drawsAt C D tF tJ t3 ρ).first, (drawsAt C D tF tJ t3 ρ).second) := by
  have h1 := loTake_lo C (chainsOf C D tF tJ t3).annJ D.ds₁ ρ.2
  have h2 := loSkip_lo C (chainsOf C D tF tJ t3).ann₃ D.ds₂ ((chainsOf C D tF tJ t3).rhoJ ρ).2
  have h3 := loEnd_lo C D.ds₃ ((chainsOf C D tF tJ t3).rho₃ ρ)
  show ((loTake C D.ds₁ (Iop.Rho.lo (Iop.RoundSplits.app (Iop.RoundSplits.allLocal (uLT C D.ds₁))
    (chainsOf C D tF tJ t3).annJ) ρ.2)).1 ++ [⟨[], [], [], none⟩],
      loEnd C D.ds₃ (loSkip C D.ds₂ (loTake C D.ds₁ (Iop.Rho.lo (Iop.RoundSplits.app
        (Iop.RoundSplits.allLocal (uLT C D.ds₁)) (chainsOf C D tF tJ t3).annJ) ρ.2)).2.2).2) = _
  rw [h1]
  show (_, loEnd C D.ds₃ (loSkip C D.ds₂ (Iop.Rho.lo (Iop.RoundSplits.app (Iop.RoundSplits.const
           (Iop.RAnn.ofShared .sh) (uLT C D.ds₂)) (chainsOf C D tF tJ t3).ann₃)
      ((chainsOf C D tF tJ t3).rhoJ ρ).2)).2) = _
  rw [h2]
  show (_, loEnd C D.ds₃ (Iop.Rho.lo (Iop.RoundSplits.allLocal (uLT C D.ds₃))
    ((chainsOf C D tF tJ t3).rho₃ ρ))) = _
  rw [h3]
  rfl

theorem drawsSh_at (ρ : Iop.Rho (chainsOf C D tF tJ t3).sh) :
    drawsSh C D tF tJ t3 (Iop.Rho.sh (chainsOf C D tF tJ t3).ann ρ) =
      (drawsAt C D tF tJ t3 ρ).shared := by
  have h1 := shSkip_sh C (chainsOf C D tF tJ t3).annJ D.ds₁ ρ.2
  have h2 := shTake_sh C (chainsOf C D tF tJ t3).ann₃ D.ds₂ ((chainsOf C D tF tJ t3).rhoJ ρ).2
  show (shTake C D.ds₂ (shSkip C D.ds₁ (Iop.Rho.sh (Iop.RoundSplits.app (Iop.RoundSplits.allLocal
           (uLT C D.ds₁)) (chainsOf C D tF tJ t3).annJ) ρ.2)).2).1 = _
  rw [h1]
  show (shTake C D.ds₂ (Iop.Rho.sh (Iop.RoundSplits.app (Iop.RoundSplits.const (Iop.RAnn.ofShared .sh)
           (uLT C D.ds₂)) (chainsOf C D tF tJ t3).ann₃) ((chainsOf C D tF tJ t3).rhoJ ρ).2)).1 = _
  rw [h2]
  rfl

end

/-! ## 2 With what the second stops may read, and with nothing -/

/-- `a`: whether something stops at what the second stops may read. `b`: whether it stops with
nothing supplied. -/
def StopRel (a b : Option Why) : Prop :=
  (b.isSome = true → a.isSome = true) ∧ (a = some .bad → b.isSome = true) ∧
    ∀ y, a = some y → y = .bad ∨ y = .hid

theorem StopRel.none : StopRel none none :=
  ⟨fun h => h, fun h => (by cases h), fun _ h => (by cases h)⟩

theorem StopRel.or {a b a' b' : Option Why} (h : StopRel a b) (h' : StopRel a' b') :
    StopRel (a.or a') (b.or b') := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨k1, k2, k3⟩ := h'
  cases a with
  | some y =>
    refine ⟨fun _ => rfl, fun e => ?_, fun z e => h3 z e⟩
    have hb := h2 e
    cases b with
    | none => cases hb
    | some _ => rfl
  | none =>
    have hb : b = Option.none := by
      cases b with
      | none => rfl
      | some _ => cases h1 rfl
    subst hb
    exact ⟨k1, k2, k3⟩

theorem StopRel.iff {a b : Option Why} (h : StopRel a b) :
    a.isSome = true ↔ b.isSome = true ∨ a = some .hid := by
  obtain ⟨h1, h2, h3⟩ := h
  constructor
  · intro ha
    cases a with
    | none => cases ha
    | some y =>
      rcases h3 y rfl with rfl | rfl
      · exact Or.inl (h2 rfl)
      · exact Or.inr rfl
  · rintro (hb | rfl)
    · exact h1 hb
    · rfl

theorem stopRel_find (f g : Nat → Option Why) (hfg : ∀ j, StopRel (f j) (g j)) :
    ∀ l : List Nat, StopRel (l.findSome? f) (l.findSome? g)
  | [] => StopRel.none
  | j :: l => by
    have e1 : (j :: l).findSome? f = (f j).or (l.findSome? f) := by
      cases h : f j <;> simp [h]
    have e2 : (j :: l).findSome? g = (g j).or (l.findSome? g) := by
      cases h : g j <;> simp [h]
    rw [e1, e2]
    exact (hfg j).or (stopRel_find f g hfg l)

theorem stopRel_part (p : Part V W Y) (v : Option V) (loc ds : List Fmt.Drawn) :
    StopRel (p.stopAt v loc ds) (p.stopAt none loc ds) := by
  unfold Part.stopAt
  refine stopRel_find _ _ (fun j => ?_) _
  by_cases hb : (p.bad loc (ds.take j)).isSome = true
  · simp only [hb, if_true]
    exact ⟨fun _ => rfl, fun _ => rfl, fun y e => Or.inl (Option.some.inj e).symm⟩
  · simp only [hb, Bool.false_eq_true, if_false, Option.bind_none, Option.isSome_none]
    by_cases hh : (v.bind fun u => p.hid u loc (ds.take j)).isSome = true
    · simp only [hh, if_true]
      exact ⟨fun h => (by cases h), fun h => (by cases h),
        fun y e => Or.inr (Option.some.inj e).symm⟩
    · simp only [hh, Bool.false_eq_true, if_false]
      exact StopRel.none

theorem stopRel_row (v : Option V) : ∀ (ps : List (Part V W Y)) (loc ds : List Fmt.Drawn),
    StopRel (rowStopAt v ps loc ds) (rowStopAt none ps loc ds)
  | [], _, _ => StopRel.none
  | p :: ps, loc, _ => (stopRel_part p v loc _).or (stopRel_row v ps _ _)

theorem stopRel_chain (v : Option V) : ∀ (bs : List (Block S Cl)) (hs : List (Placed V W Y))
    (loc ds : List Fmt.Drawn), StopRel (chainStopAt v bs hs loc ds) (chainStopAt none bs hs loc ds)
  | [], _, _, _ => StopRel.none
  | b :: bs, hs, loc, ds => by
    refine StopRel.or ?_ (stopRel_chain v bs hs _ _)
    cases hs.find? fun h => h.place == b.place with
    | none => exact StopRel.none
    | some h => exact stopRel_row v h.parts _ _

theorem isSome_or {α : Type} (a b : Option α) :
    (a.or b).isSome = true ↔ a.isSome = true ∨ b.isSome = true := by
  cases a <;> cases b <;> simp

/-! ## 3 The abort set of `honestB` -/

/-- The abort set (`withheld`) reads a verifier's message through `drawsAt` alone: at every private
input and instance, with a trace or without. -/
theorem withheld_reads (C : CK) (D : WholeD) (tF : TF) (tJ : TJ) (t3 : T3) (F : FileDescription Xi)
    (silent : Xi → TF → TJ → T3 → Bool) (B : ProverCoinCounts) (H : Prover W₀ Rc Xi Ky Tr X₀ X) [Fintype R2]
    [Nonempty R2] [Fintype R3] [Inhabited R3] (J : R2 → R3 → KeyAndJoiningRoundMessages W₀ Rc Sd Xi Ky TF TJ T3)
    (ext : W₀ × Rc × Sd → (Iop.oneExternalString (2 ^ D.a) SgX).Str) (w : W₀ × Rc × Sd) (x : Xi)
    (ρ : Iop.Rho (chainsOf C D tF tJ t3).sh) :
    ρ ∈ (honestB C D tF tJ t3 F silent B H J ext).one.withheld w x ↔
      (badB F H ((drawsAt C D tF tJ t3 ρ).first, (drawsAt C D tF tJ t3 ρ).second) = true ∨
        stop0B F H (drawsAt C D tF tJ t3 ρ).shared = true) ∨
      hidB F H w.1 w.2.1 x ((drawsAt C D tF tJ t3 ρ).first, (drawsAt C D tF tJ t3 ρ).second) =
        true := by
  have hL : ρ ∈ (honestB C D tF tJ t3 F silent B H J ext).one.withheld w x ↔
      (badB F H (drawsLo C D tF tJ t3 (Iop.Rho.lo (chainsOf C D tF tJ t3).ann ρ)) = true ∨
        stop0B F H (drawsSh C D tF tJ t3 (Iop.Rho.sh (chainsOf C D tF tJ t3).ann ρ)) = true) ∨
      hidB F H w.1 w.2.1 x (drawsLo C D tF tJ t3 (Iop.Rho.lo (chainsOf C D tF tJ t3).ann ρ)) =
        true := Iff.rfl
  rw [hL, drawsLo_at, drawsSh_at]

theorem withheld_iff (C : CK) (D : WholeD) (tF : TF) (tJ : TJ) (t3 : T3) (F : FileDescription Xi)
    (silent : Xi → TF → TJ → T3 → Bool) (B : ProverCoinCounts) (H : Prover W₀ Rc Xi Ky Tr X₀ X) [Fintype R2]
    [Nonempty R2] [Fintype R3] [Inhabited R3] (J : R2 → R3 → KeyAndJoiningRoundMessages W₀ Rc Sd Xi Ky TF TJ T3)
    (ext : W₀ × Rc × Sd → (Iop.oneExternalString (2 ^ D.a) SgX).Str) (w : W₀ × Rc × Sd) (x : Xi)
    (htr : (H.trace w.1 x).isSome = true) (ρ : Iop.Rho (chainsOf C D tF tJ t3).sh) :
    ρ ∈ (honestB C D tF tJ t3 F silent B H J ext).one.withheld w x ↔
      (silentAt F H w.1 w.2.1 x (drawsAt C D tF tJ t3 ρ)).isSome = true := by
  obtain ⟨tr, htr'⟩ := Option.isSome_iff_exists.1 htr
  rw [withheld_reads]
  generalize drawsAt C D tF tJ t3 ρ = δ
  have r1 := (stopRel_chain (Face.own.sees (⟨w.1, w.2.1, x, tr⟩ : Local W₀ Rc Xi Tr))
    F.first.blocksInOrder H.first [] δ.first).iff
  have r3 := (stopRel_chain (Face.own.sees (⟨w.1, w.2.1, x, tr⟩ : Local W₀ Rc Xi Tr))
    F.second.blocksInOrder H.second δ.first δ.second).iff
  unfold silentAt badB stop0B hidB
  rw [htr']
  simp only [Option.bind_some, Option.any_some, Bool.or_eq_true, beq_iff_eq, isSome_or]
  rw [r1, r3]
  have e : Face.shared.sees (⟨w.1, w.2.1, H.key x⟩ : Common W₀ Rc Ky) = (none : Option Empty) := rfl
  rw [e]
  tauto

theorem withheld_congr (C : CK) (D : WholeD) (tF : TF) (tJ : TJ) (t3 : T3) (F : FileDescription Xi)
    (silent : Xi → TF → TJ → T3 → Bool) (B : ProverCoinCounts) (H : Prover W₀ Rc Xi Ky Tr X₀ X) [Fintype R2]
    [Nonempty R2] [Fintype R3] [Inhabited R3] (J : R2 → R3 → KeyAndJoiningRoundMessages W₀ Rc Sd Xi Ky TF TJ T3)
    (ext : W₀ × Rc × Sd → (Iop.oneExternalString (2 ^ D.a) SgX).Str) (w : W₀ × Rc × Sd) (x : Xi)
    (ρ ρ' : Iop.Rho (chainsOf C D tF tJ t3).sh)
    (h : drawsAt C D tF tJ t3 ρ = drawsAt C D tF tJ t3 ρ') :
    ρ ∈ (honestB C D tF tJ t3 F silent B H J ext).one.withheld w x ↔
      ρ' ∈ (honestB C D tF tJ t3 F silent B H J ext).one.withheld w x := by
  rw [withheld_reads, withheld_reads, h]

end ProofFile.Honest

#print axioms ProofFile.Honest.loTake_lo
#print axioms ProofFile.Honest.loSkip_lo
#print axioms ProofFile.Honest.shTake_sh
#print axioms ProofFile.Honest.shSkip_sh
#print axioms ProofFile.Honest.loEnd_lo
#print axioms ProofFile.Honest.drawsLo_at
#print axioms ProofFile.Honest.drawsSh_at
#print axioms ProofFile.Honest.StopRel.none
#print axioms ProofFile.Honest.StopRel.or
#print axioms ProofFile.Honest.StopRel.iff
#print axioms ProofFile.Honest.stopRel_find
#print axioms ProofFile.Honest.stopRel_part
#print axioms ProofFile.Honest.stopRel_row
#print axioms ProofFile.Honest.stopRel_chain
#print axioms ProofFile.Honest.isSome_or
#print axioms ProofFile.Honest.withheld_reads
#print axioms ProofFile.Honest.withheld_iff
#print axioms ProofFile.Honest.withheld_congr
