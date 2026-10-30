-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/LineAt.lean: the rounds and the wire record of a whole file (OnBytes/Maker/Whole.lean,
`chainsOf`; OnBytes/Maker/Wire.lean, `wqWhole`) meet what OnBytes/TypedOracleCompiler/Joined/K/RunsLine.lean asks of
a file's rounds and wire records.

Why. What is shown in OnBytes/TypedOracleCompiler/Run/ of a hash chain's run over written rounds stands at one
chain's wire records, without a tail: a first round's record, then `wiresSL` or `wShE`. The compiled
verifier of a file runs each chain at `wire₁`, `wire₂`, `wire₃` of the file's record
(OnBytes/TypedOracleCompiler/Joined/Verifier.lean). K/RunsLine.lean joins the two under hypotheses on the file's
rounds and wire records. Here these hypotheses are shown at our value.

  `plainRS`, `plainRS_up`: a round that sends a plain part alone, as a skeleton of a round
    (Run/TwinDefs.lean, `RS`); as a round it is Compile/Joined/Types.lean's `plainRound`, by
    unfolding.
  `chainsOf_line`: the rounds of a whole file are K/RunsLine.lean's `chainsL`, by unfolding.
  `wire₁_whole`, `wire₂_whole`, `wire₃_whole`: each chain's records are its silent round's record
    and the records of its written rounds.
  `wire₁_line`, `wire₃_line`, `wiresSh_line`: across types, the first and the third chain's records
    are the silent round's and `wiresSL` (OnBytes/TypedOracleCompiler/Run/PlanQS.lean), and a shared chain's written
    rounds' are `wShE` (OnBytes/TypedOracleCompiler/Run/ChainEndSh.lean), at the data without the stored tables. The
    annotations on the two sides are equal by theorems (`Twin.allLo_eq`, `annShE_eq`), not by
    unfolding.
  `eq_cast_of_heq`, `eq_wTo_of_heq`: tools: records that are one across two annotations are one
    along an equation of these.
  `hw₁`, `hw₂`, `hw₃`: the three equations on the file's wire records, in K/RunsLine.lean's own
    form.
  `wireSilent_depthJ`, `wireSilent_depth0`, `joinKind`: a silent round's record has no tree; the
    joining round is shared.

What is not claimed. Nothing on a run, on a family of hash functions, on a reader, on the roots or
the plain parts of a proof string: of what K/RunsLine.lean and K/RunsLineRead.lean ask, this file
pays what speaks of the rounds and the wire records alone.


-/
import OnBytes.Maker.TreesLine
import OnBytes.TypedOracleCompiler.Joined.Verifier
import OnBytes.TypedOracleCompiler.Joined.K.RunsLine

set_option autoImplicit false

namespace OnBytes.Maker

open TypedOracleCompiler.Iop TypedOracleCompiler.Joined _root_.Compile.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ
open _root_.Run.Twin (RS)

/-- A round that sends a plain part alone, as a skeleton. -/
@[reducible] def plainRS (T : Type) (t : T) : RS where
  Orc := Unit
  Pos := Empty
  Sym := fun _ => Unit
  rd := fun _ p => p.elim
  Plain := T
  Chal := Unit
  dOrc := ()
  dPlain := t
  finT := fun _ => inferInstance
  ne := inferInstance

theorem plainRS_up (T : Type) (t : T) : (plainRS T t).up = plainRound T t := rfl

/-- Wire records that are one across two annotations are one along an equation of these. -/
theorem eq_cast_of_heq {K : ℕ} {s : Shape} {A A' : RoundSplits s} (h : A = A')
    (W : RoundsQueryLayout 256 K s A) (V : RoundsQueryLayout 256 K s A') (hv : HEq V W) : V = h ▸ W := by
  subst h
  exact eq_of_heq hv

section
variable (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (D : WholeD)
  {TF TJ T3 Xi : Type} (tF : TF) (tJ : TJ) (t3 : T3) (silent : Xi → TF → TJ → T3 → Bool)
  (run : Xi → View → View → View → Bool)

theorem wire₁_whole : wire₁ (wqWhole C K chal D tF tJ t3 silent run) =
    (wireSilent (K + 1) TF tF _, wiresLo C K chal D.ds₁) :=
  congrArg (Prod.mk (wireSilent (K + 1) TF tF _)) (WireSB.fst_app _ _)

theorem wire₂_whole : wire₂ (wqWhole C K chal D tF tJ t3 silent run) =
    (wireSilent (K + 1) TJ tJ _, wiresSh C K chal D.ds₂) := by
  unfold wire₂
  show WireSB.fst (WireSB.snd (WireSB.app (wiresLo C K chal D.ds₁) _)) = _
  rw [WireSB.snd_app]
  exact congrArg (Prod.mk (wireSilent (K + 1) TJ tJ _)) (WireSB.fst_app _ _)

theorem wire₃_whole : wire₃ (wqWhole C K chal D tF tJ t3 silent run) =
    (wireSilent (K + 1) T3 t3 _, wiresLo C K chal D.ds₃) := by
  unfold wire₃
  show WireSB.snd (WireSB.snd (WireSB.app (wiresLo C K chal D.ds₁) _)) = _
  rw [WireSB.snd_app]
  show WireSB.snd (WireSB.app (wiresSh C K chal D.ds₂) _) = _
  rw [WireSB.snd_app]
  rfl

/-- **The first chain's wire records are, across types, those of OnBytes/TypedOracleCompiler/Run/PlanQS.lean**
behind the front round's. -/
theorem wire₁_line : HEq (wire₁ (wqWhole C K chal D tF tJ t3 silent run))
    ((wireSilent (K + 1) TF tF (plainRS TF tF).lo, TypedOracleCompiler.Run.PQ.wiresSL C K chal (toRDs D.ds₁)) :
      RoundsQueryLayout 256 (K + 1) (Twin.up (plainRS TF tF :: SLT C D.ds₁))
        (Twin.allLo (plainRS TF tF :: SLT C D.ds₁))) := by
  rw [wire₁_whole]
  exact heq_cons K (RAnn.allLocal (plainRound TF tF)) (wireSilent (K + 1) TF tF _)
    (Twin.allLo_eq (SLT C D.ds₁)).symm (wiresLo C K chal D.ds₁)
    (TypedOracleCompiler.Run.PQ.wiresSL C K chal (toRDs D.ds₁)) (wiresLo_line C K chal D.ds₁)

/-- The same for the third chain, behind the seam's. -/
theorem wire₃_line : HEq (wire₃ (wqWhole C K chal D tF tJ t3 silent run))
    ((wireSilent (K + 1) T3 t3 (plainRS T3 t3).lo, TypedOracleCompiler.Run.PQ.wiresSL C K chal (toRDs D.ds₃)) :
      RoundsQueryLayout 256 (K + 1) (Twin.up (plainRS T3 t3 :: SLT C D.ds₃))
        (Twin.allLo (plainRS T3 t3 :: SLT C D.ds₃))) := by
  rw [wire₃_whole]
  exact heq_cons K (RAnn.allLocal (plainRound T3 t3)) (wireSilent (K + 1) T3 t3 _)
    (Twin.allLo_eq (SLT C D.ds₃)).symm (wiresLo C K chal D.ds₃)
    (TypedOracleCompiler.Run.PQ.wiresSL C K chal (toRDs D.ds₃)) (wiresLo_line C K chal D.ds₃)

end

/-! ## Against OnBytes/TypedOracleCompiler/Joined/K/RunsLine.lean -/

open TypedOracleCompiler.Joined.K (chainsL wTo annL₂ annW₂ wireW₂)

/-- **The rounds of a whole file are `chainsL`'s**, by unfolding. -/
theorem chainsOf_line (C : CK) (D : WholeD) {TF TJ T3 : Type} (tF : TF) (tJ : TJ) (t3 : T3) :
    chainsOf C D tF tJ t3 =
      chainsL C (plainRS TF tF) (plainRS TJ tJ) (plainRS T3 t3) (RAnn.ofShared .sh _)
        (toRDs D.ds₁) (toRDs D.ds₂) (toRDs D.ds₃) := rfl

/-- Wire records that are one across two annotations are one along an equation of these. -/
theorem eq_wTo_of_heq {K : ℕ} {s : Shape} {A A' : RoundSplits s} (h : A = A') (W : RoundsQueryLayout 256 K s A)
    (V : RoundsQueryLayout 256 K s A') (hv : HEq V W) : V = wTo h W := by
  subst h
  exact eq_of_heq hv

section
variable (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)

/-- **A shared chain's wire records are those of OnBytes/TypedOracleCompiler/Run/ChainEndSh.lean**, across types. -/
theorem wiresSh_line : ∀ ds : List RDT,
    HEq (wiresSh C K chal ds) (TypedOracleCompiler.Run.PQ.wShE C K chal (toRDs ds))
  | [] => HEq.rfl
  | d :: ds =>
    heq_cons K (RAnn.ofShared .sh (roundT C d).up) (wireSh C K chal d)
      (TypedOracleCompiler.Run.PQ.annShE_eq C (toRDs ds)).symm (wiresSh C K chal ds)
      (TypedOracleCompiler.Run.PQ.wShE C K chal (toRDs ds)) (wiresSh_line ds)

variable (D : WholeD) {TF TJ T3 Xi : Type} (tF : TF) (tJ : TJ) (t3 : T3)
  (silent : Xi → TF → TJ → T3 → Bool) (run : Xi → View → View → View → Bool)

/-- **The first chain's equation.** -/
theorem hw₁ : wire₁ (wqWhole C K chal D tF tJ t3 silent run) =
    wTo (Twin.allLo_eq (plainRS TF tF :: TypedOracleCompiler.Run.PQ.SL C (toRDs D.ds₁)))
      (wireSilent (K + 1) TF tF (plainRS TF tF).lo, TypedOracleCompiler.Run.PQ.wiresSL C K chal (toRDs D.ds₁)) :=
  eq_wTo_of_heq _ _ _ (wire₁_line C K chal D tF tJ t3 silent run)

/-- **The third chain's.** -/
theorem hw₃ : wire₃ (wqWhole C K chal D tF tJ t3 silent run) =
    wTo (Twin.allLo_eq (plainRS T3 t3 :: TypedOracleCompiler.Run.PQ.SL C (toRDs D.ds₃)))
      (wireSilent (K + 1) T3 t3 (plainRS T3 t3).lo, TypedOracleCompiler.Run.PQ.wiresSL C K chal (toRDs D.ds₃)) :=
  eq_wTo_of_heq _ _ _ (wire₃_line C K chal D tF tJ t3 silent run)

/-- **The second chain's.** -/
theorem hw₂ : wire₂ (wqWhole C K chal D tF tJ t3 silent run) =
    wTo (annL₂ C (plainRS TF tF) (plainRS TJ tJ) (plainRS T3 t3) (RAnn.ofShared .sh _)
        (toRDs D.ds₁) (toRDs D.ds₂) (toRDs D.ds₃))
      (wireW₂ C K chal (plainRS TJ tJ) (RAnn.ofShared .sh _) (wireSilent (K + 1) TJ tJ _)
        (toRDs D.ds₂)) := by
  refine eq_wTo_of_heq _ _ _ ?_
  rw [wire₂_whole]
  exact heq_cons K (RAnn.ofShared .sh (plainRound TJ tJ)) (wireSilent (K + 1) TJ tJ _)
    (TypedOracleCompiler.Run.PQ.annShE_eq C (toRDs D.ds₂)).symm (wiresSh C K chal D.ds₂)
    (TypedOracleCompiler.Run.PQ.wShE C K chal (toRDs D.ds₂)) (wiresSh_line C K chal D.ds₂)

end

/-! ### The silent rounds' records have no tree -/

theorem wireSilent_depthJ (K : ℕ) (T : Type) (t : T) (a : RAnn (plainRound T t)) :
    (wireSilent K T t a).depthJ = [] := rfl

theorem wireSilent_depth0 (K : ℕ) (T : Type) (t : T) (a : RAnn (plainRound T t)) :
    (wireSilent K T t a).depth0 = [] := rfl

theorem joinKind (T : Type) (t : T) : (RAnn.ofShared .sh (plainRound T t)).kind = Kind.sh := rfl

end OnBytes.Maker
