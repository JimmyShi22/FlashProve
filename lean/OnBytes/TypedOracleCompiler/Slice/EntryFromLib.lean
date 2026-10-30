-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/EntryFromLib.lean: from the library's limits, bounds, soundness and count at a
description to the sibling's, where no round sends more than one root. The compiler under
OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made with; it builds on definitions of
Compile/.

"The line": the files of OnBytes/Slice/ and OnBytes/Tie/, over the library's compiler.

WHY. What the line has shown of the entry's description, at the full size too, it has shown in the
library's notions: rounds' data with at most one tree a round. The sibling's rounds' data have a
list of trees a round. Within the library's limits no round sends more than one root, and there the
sibling's rounds' data are the library's taken over (`PQ.rds_ofLib`, `PQ.ofLib`:
OnBytes/TypedOracleCompiler/Run/PlanQJoin.lean). This file carries along that equation what
OnBytes/TypedOracleCompiler/Slice/PartChainStr.lean asks. ALL OF IT IS STATED FOR VARIABLES: no closed term is
evaluated here, but for 1 ≤ `maxRt`.

NEW (17). AS TEXT (1): `fitL_length`. TURNED (1): `rootsFit_of` (the frame of the library's lemma of
that name, Run/OneIsTypedTop.lean, with another core). Most declarations name the library's notions
beside their namesakes, on purpose.
 `nOpen_ofLib`, `depthOf_toList`, `maxDepth_ofLib`, `okX_ofLib`   count of openings, depths and the
                      limits on stored tables' openings, at rounds' data taken over: equations.
 `roots_le_one`, `ok_of_lib`, `work_of_lib`   within the library's `ok`: at most one root a round;
                      the sibling's `ok`; the condition on work.
 `rootsFit_of`, `fitL_length`, `fitsS_of_lib`   the sibling's bounds `FitsS` from the library's
                      `FitsS` and the number of rounds, over the sibling's `FitL`.
 `ds_asTypedCompilerDescription`, `ok_asTypedCompilerDescription`, `soundLT_of_lib`, `xdOf_eq`   at a description with stored tables, taken
                      over by `asTypedCompilerDescription` (OnBytes/TypedOracleCompiler/Slice/EntryAccept.lean): rounds' data; the limits
                      `XD.ok`; THE LINE'S `SoundLAny` GIVES `SoundLT`, whatever the bodies (by
                      `sound_xd`); the sibling's `xdOf S stm` is `asTypedCompilerDescription` of the line's, by
                      definition.
 `wireTo_nOpen`, `wireTo_nOpen_lib`, `length_uL`, `length_uL_lib`, `tVQB_asTypedCompilerDescription`   THE SIBLING'S
                      BOUND ON THE LINK VERIFIER'S QUERIES AT ITS WIRING IS THE LIBRARY'S AT THE
                      LINE'S WIRING.

WHAT IT IMPORTS OF THE LINE: OnBytes/Slice/TopAny.lean, and through
OnBytes/TypedOracleCompiler/Slice/PartChainAsk.lean more; files of OnBytes/Hash/ stand under these.

WHAT IS NOT SAID. The converse of any implication: the sibling's limits allow two roots a round.
Nothing at a description with a round of two roots. Nothing on soundness beyond the carrying of a
hypothesis; no probability.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.EntryAccept
import OnBytes.TypedOracleCompiler.Slice.PartChainAsk
import OnBytes.Slice.TopAny
import Run.OneIsTypedTop

set_option autoImplicit false

namespace TypedOracleCompiler.Slice
open Rom Prob _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop MeasureTheory
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run.PQ (View SgX XO)
open TypedOracleCompiler.Run
open TypedOracleCompiler.Run.PQ (XD BodyD OwnE WkAny FitsS RootsFit)
open TypedOracleCompiler.Slice.EntryAccept (asTypedCompilerDescription sound_xd)
open scoped ENNReal

/-! ## Rounds' data with at most one tree a round -/

section
variable (ds : List _root_.Run.PQ.RD)

/-- The sibling's count of opened positions, at the library's rounds' data taken over, is the
library's. -/
theorem nOpen_ofLib : PQ.nOpen (ds.map PQ.ofLib) = _root_.Run.PQ.nOpen ds := by
  unfold PQ.nOpen _root_.Run.PQ.nOpen
  rw [List.map_map]
  rfl

/-- The sibling's depth of a list of at most one tree is the library's depth of that tree. -/
theorem depthOf_toList (t : Option _root_.Fmt.Shape) :
    PQ.depthOf t.toList = _root_.Run.PQ.depthOf t := by
  cases t with
  | none => rfl
  | some s => exact Nat.zero_max s.a

/-- The sibling's greatest depth, at the library's rounds' data taken over, is the library's. -/
theorem maxDepth_ofLib : PQ.maxDepth (ds.map PQ.ofLib) = _root_.Run.PQ.maxDepth ds := by
  unfold PQ.maxDepth _root_.Run.PQ.maxDepth
  rw [List.foldl_map]
  congr 1
  funext a d
  show max a (PQ.depthOf d.tree.toList) = _
  rw [depthOf_toList]

/-- The sibling's limits on the stored tables' openings, at the library's rounds' data taken over,
are the library's. -/
theorem okX_ofLib (a : ℕ) (xs : List XO) :
    PQ.okX (ds.map PQ.ofLib) a xs = _root_.Run.PQ.okX ds a xs := by
  unfold PQ.okX _root_.Run.PQ.okX
  congr 1
  · congr 1
    congr 1
    · refine congrArg (List.all xs) (funext fun o => ?_)
      rw [List.getElem?_map]
      cases ds[o.round]? <;> rfl
    · rw [List.zipIdx_map, List.all_map]
      rfl
  · rw [List.all_map]
    rfl

end

/-! ## A description within the library's limits -/

section
variable (S : _root_.Fmt.Spec)

/-- Within the library's limits no round sends more than one root. -/
theorem roots_le_one (h : _root_.Run.PQ.ok S = true) : ∀ r ∈ S.rounds, r.entry.roots ≤ 1 := by
  simp only [_root_.Run.PQ.ok, Bool.and_eq_true, and_assoc] at h
  intro r hr
  exact of_decide_eq_true (List.all_eq_true.1 h.2.1 r hr)

/-- The library's limits imply the sibling's. -/
theorem ok_of_lib (h : _root_.Run.PQ.ok S = true) : PQ.ok S = true := by
  have h1 := roots_le_one S h
  simp only [_root_.Run.PQ.ok, Bool.and_eq_true, and_assoc] at h
  simp only [PQ.ok, Bool.and_eq_true, and_assoc]
  refine ⟨h.1, ?_, h.2.2⟩
  exact List.all_eq_true.2 fun r hr => decide_eq_true (le_trans (h1 r hr) (by decide))

/-- The condition on work passes over. -/
theorem work_of_lib (h : _root_.Run.PQ.ok S = true)
    (hw : (_root_.Run.PQ.rds S).all (fun d => decide (d.entry.work ≤ 64)) = true) :
    ∀ d ∈ PQ.rds S, d.entry.work ≤ 64 := by
  rw [PQ.rds_ofLib S (roots_le_one S h)]
  intro d hd
  obtain ⟨d', hd', rfl⟩ := List.mem_map.1 hd
  exact of_decide_eq_true (List.all_eq_true.1 hw d' hd')

/-- As many roots as a round has trees fit the round's items, along the sibling's `FitL`. -/
theorem rootsFit_of : ∀ (ds : List PQ.RD) (rs : List _root_.Fmt.Round), PQ.FitL ds rs → RootsFit ds
  | [], _, _, _, hd, _, _ => by cases hd
  | _ :: _, [], hf, _, _, _, _ => hf.elim
  | d :: ds, r :: rs, hf, d', hd, rt, hrt => by
    obtain ⟨-, -, h3, h4, h5, -, h7⟩ := hf
    rcases List.mem_cons.1 hd with rfl | hd
    · exact PQ.toRoots_isSome _ rt (by rw [h3, h5, hrt, h4])
    · exact rootsFit_of ds rs h7 d' hd rt hrt

/-- The sibling's rounds' data are as many as the rounds. -/
theorem fitL_length : ∀ (ds : List PQ.RD) (rs : List _root_.Fmt.Round), PQ.FitL ds rs →
    ds.length = rs.length
  | [], [], _ => rfl
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim
  | _ :: ds, _ :: rs, h => by
    rw [List.length_cons, List.length_cons, fitL_length ds rs h.2.2.2.2.2.2]

/-- The sibling's bounds `FitsS` from the library's, within the library's `ok`, with fewer than
2^64 rounds. -/
theorem fitsS_of_lib (K : ℕ) (h : _root_.Run.PQ.ok S = true) (F : _root_.Run.PQ.FitsS S K)
    (hlen : S.rounds.length < 2 ^ 64) : FitsS S K where
  k48 := F.k48
  work := F.work
  roots := rootsFit_of (PQ.rds S) S.rounds (PQ.fit_rds S (ok_of_lib S h))
  len := by rw [fitL_length (PQ.rds S) S.rounds (PQ.fit_rds S (ok_of_lib S h))]; exact hlen
  salt := F.salt

end

/-! ## A description with stored tables -/

section
variable (D : _root_.Run.PQ.XD)

/-- The sibling's rounds' data of the description taken over. -/
theorem ds_asTypedCompilerDescription (h : _root_.Run.PQ.ok D.base = true) : (asTypedCompilerDescription D).ds = D.ds.map PQ.ofLib :=
  PQ.rds_ofLib D.base (roots_le_one D.base h)

/-- The library's limits on a description with stored tables imply the sibling's. -/
theorem ok_asTypedCompilerDescription (h : D.ok = true) : (asTypedCompilerDescription D).ok = true := by
  unfold _root_.Run.PQ.XD.ok at h
  simp only [Bool.and_eq_true] at h
  unfold XD.ok
  simp only [Bool.and_eq_true]
  refine ⟨⟨ok_of_lib D.base h.1.1, ?_⟩, h.2⟩
  rw [ds_asTypedCompilerDescription D h.1.1]
  exact (okX_ofLib D.ds D.a D.xs).trans h.1.2

/-- The one hypothesis passes over: the line's `SoundLAny` gives `SoundLT`, whatever the type of
bodies. By `sound_xd`. -/
theorem soundLT_of_lib (Bd : Type) (dec : View → Bool) (h : _root_.Run.PQ.ok D.base = true)
    (Lg : Unit → (twoExternalStrings (2 ^ D.a) SgX).Str → Prop) (e : ℝ≥0∞)
    (hs : OnBytes.Slice.SoundLAny D dec Lg e) : SoundLT Bd (asTypedCompilerDescription D) dec Lg e :=
  sound_xd Bd D dec (roots_le_one D.base h) Lg e hs

/-- The sibling's description made from a description of the format is the library's, taken over. By
definition. -/
theorem xdOf_eq (S : _root_.Fmt.SpecX) (stm : ByteArray → ByteArray → ByteArray) :
    PQ.xdOf S stm = asTypedCompilerDescription (OnBytes.Tie.xdOf S stm) := rfl

end

/-! ## The number of the compiled Link verifier's queries -/

/-- The number of a wiring's openings goes along an equation between two batch protocols. -/
theorem wireTo_nOpen {Y : Type} {E : ExtSpec} {lam K : ℕ} {Q Q' : BatchInteractiveOracleProof Y E} (h : Q = Q')
    (w : ProtocolQueryLayout lam K Q) : (PQ.wireTo h w).nOpen = w.nOpen := by
  subst h
  rfl

/-- The same for the line's carrying of the library's wirings. -/
theorem wireTo_nOpen_lib {Y : Type} {E : ExtSpec} {lam K : ℕ} {Q Q' : BatchInteractiveOracleProof Y E} (h : Q = Q')
    (w : _root_.Iop.ProtocolQueryLayout lam K Q) : (OnBytes.Slice.wireTo h w).nOpen = w.nOpen := by
  subst h
  rfl

/-- The sibling's shape of a list of rounds' data has as many rounds as the list. -/
theorem length_uL (C : _root_.Run.PQ.CK) : ∀ ds : List PQ.RD, (PQ.uL C ds).length = ds.length
  | [] => rfl
  | _ :: ds => congrArg (· + 1) (length_uL C ds)

/-- So has the library's. -/
theorem length_uL_lib (C : _root_.Run.PQ.CK) : ∀ ds : List _root_.Run.PQ.RD, (_root_.Run.PQ.uL C
    ds).length = ds.length
  | [] => rfl
  | _ :: ds => congrArg (· + 1) (length_uL_lib C ds)

section
variable {Bd : Type} (B : BodyD Bd) (D : _root_.Run.PQ.XD) (dec : View → Bool) (E : OwnE Bd (asTypedCompilerDescription
    D))

/-- The sibling's bound on the compiled Link verifier's queries, at the wiring of a description
within the library's limits, is the library's bound at the line's wiring of that description. Both
are one formula of the number of rounds, the number of openings and the greatest depth, and these
agree where no round has more than one tree. -/
theorem tVQB_asTypedCompilerDescription (h : _root_.Run.PQ.ok D.base = true) :
    tVQB (WkAny B (asTypedCompilerDescription D) dec E).Lk (WkAny B (asTypedCompilerDescription D) dec E).depthReqL =
      _root_.Compile.Batch.tVQB (OnBytes.Slice.WkAny D dec).Lk
        (OnBytes.Slice.WkAny D dec).depthReq := by
  have e1 : (WkAny B (asTypedCompilerDescription D) dec E).Lk.nOpen =
      PQ.nOpen (asTypedCompilerDescription D).ds + ((asTypedCompilerDescription D).xs.map (·.count)).sum := wireTo_nOpen _ _
  have e2 : (WkAny B (asTypedCompilerDescription D) dec E).Lk.maxDepth = max (PQ.maxDepth (asTypedCompilerDescription D).ds) (asTypedCompilerDescription D).a :=
    PQ.wireTo_maxDepth _ _
  have f1 : (OnBytes.Slice.WkAny D dec).Lk.nOpen = _root_.Run.PQ.nOpen D.ds + (D.xs.map
      (·.count)).sum :=
    wireTo_nOpen_lib _ _
  have f2 : (OnBytes.Slice.WkAny D dec).Lk.maxDepth = max (_root_.Run.PQ.maxDepth D.ds) D.a :=
    OnBytes.Slice.wireTo_maxDepth _ _
  have l1 : (PQ.uL (asTypedCompilerDescription D).C (asTypedCompilerDescription D).ds).length = (_root_.Run.PQ.uL D.C D.ds).length := by
    rw [length_uL, length_uL_lib, ds_asTypedCompilerDescription D h, List.length_map]
  unfold tVQB _root_.Compile.Batch.tVQB
  rw [e1, e2, f1, f2, ds_asTypedCompilerDescription D h, nOpen_ofLib, maxDepth_ofLib]
  show ((PQ.uL (asTypedCompilerDescription D).C (asTypedCompilerDescription D).ds).length + 1 + 1) + _ =
    ((_root_.Run.PQ.uL D.C D.ds).length + 1 + 1) + _
  rw [l1]
  rfl

end

end TypedOracleCompiler.Slice
