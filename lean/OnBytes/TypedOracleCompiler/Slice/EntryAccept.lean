-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/EntryAccept.lean: round-by-round soundness of the library's protocol with two
external strings passes to the sibling's protocol at the same description.

Why. The sibling of the library's soundness road (OnBytes/TypedOracleCompiler/) builds its protocols from rounds'
data with a LIST of trees a round, the library from data with at most one. At the library's data
(`ofLib`) the two protocols are alike and not equal: a round's positions are `Fin (2 ^ s.a) ⊕ Empty`
in the one and `Fin (posN (some s))` in the other, so the two shapes are two types, and a soundness
statement on the one does not even typecheck at the other. OnBytes/Slice/ShapeMap.lean carries
soundness along a map of shapes, from a given old protocol to a given new one, if whatever the new
one accepts the old one accepts on the transcript read back. OnBytes/TypedOracleCompiler/Slice/CarryOne.lean has the
map (`sOneUp`). This file shows that hypothesis, for the protocol `skeletonOverBothExternalStrings` of an entry file's chain,
and draws the conclusion.

How. Both verifiers are one text over two kinds of rounds' data: all tests of work pass, every part
has as many draws as it says, every stored symbol carries its position, and the decision accepts the
view. Each piece is walked along the list of rounds. What is drawn, the tests of work and the
rounds' records are the same by definition, round by round, since plain part and verifier's message
are one type in both. The one lemma with matter is `col_back`: the column at (tree, position).

Main theorems.
 `drawn_back`, `pass_back`, `rv_back`, `col_back` the four pieces, at a transcript and at the
     transcript read back.
 `wantedX_ofLib`, `carries_ofLib`, `view_back` what the drawn positions ask for; the test on stored
     symbols; the view.
 `accept_back` the sibling's protocol accepts a transcript exactly if the library's accepts it read
     back. An equation.
 `sound_ofLib`, `sound_of_eq` so soundness with errors below e passes: at `ds.map ofLib`, and at any
     rounds' data of the sibling that are equal to that.
 `sound_xd` at a description: the hypothesis that OnBytes/Slice/TopAny.lean calls `SoundLAny`,
     written out, passes from the library's `XD.L` to the sibling's at the same three fields,
     whatever the type of bodies, IF NO ROUND OF THE DESCRIPTION SENDS MORE THAN ONE ROOT.

What is not claimed. Nothing on a round with two roots: there the library has no protocol to carry
from. That the verifier is local is not carried, nor that the two verifiers read the same positions:
the sibling has locality as a theorem of its own (`psofX_local`,
OnBytes/TypedOracleCompiler/Run/PlanQXLawsProofs.lean). Completeness and zero knowledge are not carried. No
soundness is proved here: it is a hypothesis. Nothing on a compiler, a wiring, an encoding or bytes.
The compiler under OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made with; it builds on
definitions of Compile/.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.CarryOne
import OnBytes.TypedOracleCompiler.Run.PlanQXRun

set_option autoImplicit false

namespace TypedOracleCompiler.Slice.EntryAccept
open _root_.Iop (Err InteractiveOracleProof twoExternalStrings)
open OnBytes.Slice.ShapeMap TypedOracleCompiler.Run TypedOracleCompiler.Slice.CarryOne
open scoped ENNReal

variable (C : _root_.Run.PQ.CK)

/-- What the rounds draw. -/
theorem drawn_back : ∀ (ds : List _root_.Run.PQ.RD) (τ : _root_.Iop.Tr (PQ.uL C (ds.map PQ.ofLib))),
    PQ.drawnSL C (ds.map PQ.ofLib) (PQ.rhoSL C (ds.map PQ.ofLib) τ) =
      _root_.Run.PQ.drawnSL C ds (_root_.Run.PQ.rhoSL C ds (back (sOne C ds) τ))
  | [], _ => rfl
  | _ :: ds, (_, _, τ) =>
      congrArg (List.cons _) (drawn_back ds τ)

/-- Whether all tests of work pass. -/
theorem pass_back : ∀ (ds : List _root_.Run.PQ.RD) (τ : _root_.Iop.Tr (PQ.uL C (ds.map PQ.ofLib))),
    PQ.passSL C (ds.map PQ.ofLib) (PQ.rhoSL C (ds.map PQ.ofLib) τ) =
      _root_.Run.PQ.passSL C ds (_root_.Run.PQ.rhoSL C ds (back (sOne C ds) τ))
  | [], _ => rfl
  | _ :: ds, (_, _, τ) =>
      congrArg (and _) (pass_back ds τ)

/-- The rounds' records. -/
theorem rv_back : ∀ (ds : List _root_.Run.PQ.RD) (τ : _root_.Iop.Tr (PQ.uL C (ds.map PQ.ofLib))),
    PQ.rvSL C (ds.map PQ.ofLib) τ = _root_.Run.PQ.rvSL C ds (back (sOne C ds) τ)
  | [], _ => rfl
  | _ :: ds, (_, _, τ) =>
      congrArg (List.cons _) (rv_back ds τ)

/-- The column at (tree, position). -/
theorem col_back : ∀ (ds : List _root_.Run.PQ.RD) (τ : _root_.Iop.Tr (PQ.uL C (ds.map PQ.ofLib)))
    (n x : ℕ), PQ.colAtS C (ds.map PQ.ofLib) τ n x =
      _root_.Run.PQ.colAtS C ds (back (sOne C ds) τ) n x
  | [], _, _, _ => rfl
  | ⟨e, k, it, none, op⟩ :: ds, (_, _, τ), n, x => by
      show (if n < 0 then _ else PQ.colAtS C (ds.map PQ.ofLib) τ (n - 0) x) =
        _root_.Run.PQ.colAtS C ds (back (sOne C ds) τ) n x
      rw [if_neg (Nat.not_lt_zero n), Nat.sub_zero, col_back ds τ n x]
  | ⟨e, k, it, some s, op⟩ :: ds, (m, _, τ), n, x => by
      show (if n < 1 then (PQ.posAtT [s] n x).map (fun p => PQ.colT [s] p (m.1 p))
          else PQ.colAtS C (ds.map PQ.ofLib) τ (n - 1) x) =
        (if n = 0 then (if h : x < 2 ^ s.a then some (List.ofFn (m.1 (.inl ⟨x, h⟩))) else none)
          else _root_.Run.PQ.colAtS C ds (back (sOne C ds) τ) (n - 1) x)
      by_cases hn : n = 0
      · subst hn
        rw [if_pos Nat.one_pos, if_pos rfl]
        show (if h : x < 2 ^ s.a then some (.inl ⟨x, h⟩) else none : Option (PQ.PosT [s])).map _ = _
        by_cases h : x < 2 ^ s.a
        · rw [dif_pos h, dif_pos h]
          rfl
        · rw [dif_neg h, dif_neg h]
          rfl
      · rw [if_neg (by omega), if_neg hn, col_back ds τ (n - 1) x]

/-- What the drawn positions ask for, stored tables' positions among them. -/
theorem wantedXL_ofLib (a : ℕ) (all : List _root_.Run.PQ.RD) (xs : List _root_.Run.PQ.XO) :
    ∀ (i : ℕ) (ds : List _root_.Run.PQ.RD) (Ds : List _root_.Fmt.Drawn),
      PQ.wantedXL a (all.map PQ.ofLib) xs i (ds.map PQ.ofLib) Ds =
        _root_.Run.PQ.wantedXL a all xs i ds Ds
  | _, [], _ => rfl
  | _, _ :: _, [] => rfl
  | i, d :: ds, D :: Ds => by
      simp only [List.map_cons, PQ.wantedXL, _root_.Run.PQ.wantedXL, PQ.treeSh_ofLib,
        wantedXL_ofLib a all xs (i + 1) ds Ds]
      rfl

/-- The same from the first round on. -/
theorem wantedX_ofLib (a : ℕ) (ds : List _root_.Run.PQ.RD) (xs : List _root_.Run.PQ.XO)
    (Ds : List _root_.Fmt.Drawn) :
    PQ.wantedX a (ds.map PQ.ofLib) xs Ds = _root_.Run.PQ.wantedX a ds xs Ds :=
  wantedXL_ofLib a ds xs 0 ds Ds

/-- Every symbol read carries its position: the same test. -/
theorem carries_ofLib (a : ℕ) (ds : List _root_.Run.PQ.RD) (xs : List _root_.Run.PQ.XO)
    (Ds : List _root_.Fmt.Drawn) (y : (twoExternalStrings (2 ^ a) _root_.Run.PQ.SgX).Str) :
    PQ.symbolsCarryTheirPositions a (ds.map PQ.ofLib) xs Ds y = _root_.Run.PQ.symbolsCarryTheirPositions a ds xs Ds y := by
  unfold PQ.symbolsCarryTheirPositions _root_.Run.PQ.symbolsCarryTheirPositions PQ.xWanted _root_.Run.PQ.xWanted
  rw [wantedX_ofLib]
  rfl

/-- The view. -/
theorem view_back (ds : List _root_.Run.PQ.RD) (a : ℕ) (xs : List _root_.Run.PQ.XO)
    (y : (twoExternalStrings (2 ^ a) _root_.Run.PQ.SgX).Str)
    (τ : _root_.Iop.Tr (PQ.uL C (ds.map PQ.ofLib))) :
    PQ.viewX C (ds.map PQ.ofLib) a xs y τ =
      _root_.Run.PQ.viewX C ds a xs y (back (sOne C ds) τ) := by
  unfold PQ.viewX _root_.Run.PQ.viewX
  rw [rv_back, drawn_back, wantedX_ofLib]
  simp only [col_back]

/-- What the sibling's protocol at the library's rounds' data accepts is what the library's
accepts on the transcript read back. An equation. -/
theorem accept_back (ds : List _root_.Run.PQ.RD) (a : ℕ) (xs : List _root_.Run.PQ.XO)
    (dec : _root_.Run.PQ.View → Bool) (x : Unit) (y : (twoExternalStrings (2 ^ a) _root_.Run.PQ.SgX).Str)
    (τ : _root_.Iop.Tr (_root_.Run.Twin.up (PQ.SOf C (ds.map PQ.ofLib)))) :
    (PQ.skeletonOverBothExternalStrings C (ds.map PQ.ofLib) a xs dec).up.loc.accept x y τ =
      (_root_.Run.PQ.skeletonOverBothExternalStrings C ds a xs dec).up.loc.accept x y (back (sOneUp C ds) τ) := by
  obtain ⟨m, c, τ⟩ := τ
  show (PQ.passSL C (ds.map PQ.ofLib) (PQ.rhoSL C (ds.map PQ.ofLib) τ) &&
      _root_.Run.PQ.everyOpeningHasItsDraws xs (PQ.drawnSL C (ds.map PQ.ofLib) (PQ.rhoSL C (ds.map PQ.ofLib) τ)) &&
      PQ.symbolsCarryTheirPositions a (ds.map PQ.ofLib) xs
        (PQ.drawnSL C (ds.map PQ.ofLib) (PQ.rhoSL C (ds.map PQ.ofLib) τ)) y &&
      dec (PQ.viewX C (ds.map PQ.ofLib) a xs y τ)) = _
  rw [pass_back, drawn_back, carries_ofLib, view_back]
  rfl

/-- Round-by-round soundness with small errors passes from the library's protocol to the
sibling's at the library's rounds' data: the same language on the same pairs of strings, the same
bound on the errors. -/
theorem sound_ofLib (ds : List _root_.Run.PQ.RD) (a : ℕ) (xs : List _root_.Run.PQ.XO)
    (dec : _root_.Run.PQ.View → Bool)
    (Lg : Unit → (twoExternalStrings (2 ^ a) _root_.Run.PQ.SgX).Str → Prop) (e : ℝ≥0∞)
    (h : ∃ ε : Err (_root_.Run.PQ.skeletonOverBothExternalStrings C ds a xs dec).up.loc.shape,
      Err.Below ε e ∧ (_root_.Run.PQ.skeletonOverBothExternalStrings C ds a xs dec).up.loc.Sound Lg ε) :
    ∃ ε : Err (PQ.skeletonOverBothExternalStrings C (ds.map PQ.ofLib) a xs dec).up.loc.shape,
      Err.Below ε e ∧ (PQ.skeletonOverBothExternalStrings C (ds.map PQ.ofLib) a xs dec).up.loc.Sound Lg ε := by
  obtain ⟨ε, hb, hs⟩ := h
  obtain ⟨ε', hs', hb'⟩ := sound_below (PQ.skeletonOverBothExternalStrings C (ds.map PQ.ofLib) a xs dec).up.loc
    (_root_.Run.PQ.skeletonOverBothExternalStrings C ds a xs dec).up.loc (sOneUp C ds)
    (fun x y τ hτ => (accept_back C ds a xs dec x y τ).symm.trans hτ) Lg e
    ⟨ε, firstZero_of_flat (sOneUp C ds) (flat_sOne C ds) ε, hs, hb⟩
  exact ⟨ε', hb', hs'⟩

/-- The same at rounds' data of the sibling that are the library's. -/
theorem sound_of_eq (ds : List _root_.Run.PQ.RD) (ds' : List PQ.RD) (hd : ds' = ds.map PQ.ofLib)
    (a : ℕ) (xs : List _root_.Run.PQ.XO) (dec : _root_.Run.PQ.View → Bool)
    (Lg : Unit → (twoExternalStrings (2 ^ a) _root_.Run.PQ.SgX).Str → Prop) (e : ℝ≥0∞)
    (h : ∃ ε : Err (_root_.Run.PQ.skeletonOverBothExternalStrings C ds a xs dec).up.loc.shape,
      Err.Below ε e ∧ (_root_.Run.PQ.skeletonOverBothExternalStrings C ds a xs dec).up.loc.Sound Lg ε) :
    ∃ ε : Err (PQ.skeletonOverBothExternalStrings C ds' a xs dec).up.loc.shape,
      Err.Below ε e ∧ (PQ.skeletonOverBothExternalStrings C ds' a xs dec).up.loc.Sound Lg ε := by
  subst hd
  exact sound_ofLib C ds a xs dec Lg e h

/-- The library's description, as the sibling's: the same three fields. -/
def asTypedCompilerDescription (D : _root_.Run.PQ.XD) : PQ.XD := ⟨D.base, D.stm, D.stored⟩

/-- The one hypothesis on the library's Link at a description passes to the sibling's Link at the
same description, whatever the type of bodies, if no round of the description sends more than one
root: the same language, the same bound on the errors. The hypothesis is written out as
`SoundLAny` (OnBytes/Slice/TopAny.lean) has it. -/
theorem sound_xd (Bd : Type) (D : _root_.Run.PQ.XD) (dec : _root_.Run.PQ.View → Bool)
    (hr : ∀ r ∈ D.base.rounds, r.entry.roots ≤ 1)
    (Lg : Unit → (twoExternalStrings (2 ^ D.a) _root_.Run.PQ.SgX).Str → Prop) (e : ℝ≥0∞)
    (h : ∃ ε : Err (D.L dec).link.shape, Err.Below ε e ∧ (D.L dec).link.Sound Lg ε) :
    ∃ ε : Err ((asTypedCompilerDescription D).L Bd dec).link.shape,
      Err.Below ε e ∧ ((asTypedCompilerDescription D).L Bd dec).link.Sound Lg ε :=
  sound_of_eq D.C D.ds (asTypedCompilerDescription D).ds (PQ.rds_ofLib D.base hr) D.a D.xs dec Lg e h

end TypedOracleCompiler.Slice.EntryAccept
