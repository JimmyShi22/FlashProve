-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/BattShort.lean: the batching of several tensor rows into one, as one kind of block:
the reduction, its joints, the statement that it is knowledge sound, and what is proved beside it.

Several claims, each on a row vector times the committed matrix at a column point, with masks,
become one: the verifier draws the seed of coefficients, and a sumcheck over the k column variables
follows. The data, the joints and the draw are the library's (`BattPar`, Cb/Ld/LdBatt.lean). The
block parts from `BattPar.batt` at one place: in each round of a variable one coefficient of the
round's polynomial is not sent (`TWhole.shortRC`): meant as the program's way; not compared here.
The sumcheck has plain weights, g(0) + g(1), so the "sum" of X is 1 and the "sum" of 1 is 2: the
coefficient that is left out is the linear one.
Main names:
  `fix1`, `fix1_ok`: for each variable the power 1 is left out, with the inverse 1; that is a lawful
    choice where the "sum" of X is 1.
  `mon1_plain`, `plains_mon1`: it is 1 at plain weights, if polynomials have a degree of at least 1.
  `F₁ B`, `F₁_ok`: the choice at the batching's sumcheck.
  `R`, `eps`: the reduction, k + 2 rounds; its errors.
  `HAt B`: the statement at the data B. Bound inside: the oracles, the types of messages, of the
    further witness and of cores, a joint A0 that is carried along, the reading msg of the entries
    off the messages, and a tuple m of messages. It says: the reduction is knowledge sound
    (`Reduction.Know`) from "A0, and all claims hold" to "A0, and the one claim holds", with the
    identity as extractor, at `eps`.
  `knowAt`, `hAt`: the record `TWhole.KnowAt`, and so the statement, if 2 ≤ B.n and the coefficients
    evade zero (B.Z.OK): the library's `batt_cnt`, `batt_ok`, and `TWhole.short_knowAtC`.
  `copies`, `passes`: the oracles are only copied; the state is handed on. No premise.
  `never_rejects`: if 1 ≤ B.n the verifier puts out a statement on every transcript.
  `rounds`, `errs`, `vals`: k + 2 rounds; the evader's number, 1, and k times n; the number of
    seeds, and k + 1 times the number of elements of the field.
Limits: nothing on an honest prover. That the coefficients of a key file's chain evade zero follows
for the powers of one element from `ok_powers` (Cb/Gen/BatEvader.lean); it is not put in here. That
the errors are a plan's bounds is not shown here. The errors are bare counts for one instance:
nothing on proof of work, nothing on several instances.

-/
import Cb.G6.Join
import Cb.G6.Core
import Cb.Ld.LdBattProofs
import Cb.Ld.LdWfPre
import Ior.KnowCollRulesChainErr

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.BattShort
open Iop IOR Prob Hiop Cb TWhole Johnson.L5.Layers

section Pick
variable {R : Type} [CommRing R]

/-- For each variable: the power 1 is left out; the inverse of its "sum" is 1. -/
def fix1 : (l : List (HVar R)) → HFixs l
  | [] => ()
  | _ :: l => ((1, 1), fix1 l)

theorem fix1_ok : ∀ l : List (HVar R), (∀ v ∈ l, v.mon 1 = 1) → HFixs.OK l (fix1 l)
  | [], _ => trivial
  | v :: l, h =>
    ⟨by
      show (1 : R) * v.mon 1 = 1
      rw [one_mul, h v (List.mem_cons_self ..)],
     fix1_ok l fun w hw => h w (List.mem_cons_of_mem _ hw)⟩

end Pick

variable {E : Type} [Field E] [Fintype E]

/-- At plain weights the "sum" of X is 1. -/
theorem mon1_plain (n : ℕ) (hn : 1 ≤ n) : ((pfCube E n).var (pdPlain E n)).mon 1 = 1 := by
  have e : ((1 : Fin (n + 1)) : ℕ) = 1 := by
    rw [Fin.val_one', Nat.mod_eq_of_lt (by omega)]
  show ∑ b : Bool, (1 : E) * (if b then (1 : E) else 0) ^ (((1 : Fin (n + 1)) : ℕ)) = 1
  rw [Fintype.sum_bool, e]
  simp

theorem plains_mon1 (n : ℕ) (hn : 1 ≤ n) :
    ∀ k, ∀ v ∈ pVars (List.replicate k (pfCube E n)) (pdPlains E n k), v.mon 1 = 1
  | 0, _, h => absurd h (List.not_mem_nil)
  | k + 1, v, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact mon1_plain n hn
    · exact plains_mon1 n hn k v h

/-- The choice at the batching's sumcheck. -/
def F₁ (B : BattPar E) : ∀ st, HFixs (B.par.vars st) := fun st => fix1 (B.par.vars st)

theorem F₁_ok (B : BattPar E) (hn : 1 ≤ B.n) : ∀ st, HFixs.OK (B.par.vars st) (F₁ B st) :=
  fun _ => fix1_ok _ (plains_mon1 B.n hn B.k)

/-- The reduction. -/
noncomputable def R (B : BattPar E) (Ex : ExtSpec) : IOR ((B.Q → E) × B.St) Ex B.par.Mid Ex :=
  (IOR.draw B.Z.D B.nx Ex).seq (shortRC B.par (F₁ B) Ex)

/-- The errors. -/
noncomputable def eps (B : BattPar E) (Ex : ExtSpec) : Err (R B Ex).shape :=
  Err.app (Nums.draw Unit B.Z.D B.nx Ex B.Z.err).err (shortEC B.par Ex)

/-- The statement that the batching at the data B is knowledge sound. -/
def HAt (B : BattPar E) : Prop :=
  ∀ (Ex : ExtSpec) (M Wp Kc : Type) (A0 : Rels Kc B.St Ex (M × Wp)) (msg : M → B.J → E) (m : M),
    (R B Ex).red.Know (B.baseIn Ex A0 fun w => msg w.1).on
      (fun a wp => (B.baseIn Ex A0 fun w => msg w.1).relR a (m, wp))
      (fun b wp => (B.baseOut Ex A0 fun w => msg w.1).relR b (m, wp)) (fun _ _ wp => wp)
      (eps B Ex)

/-- The four fields, if the degree is at least 2 and the coefficients evade zero. -/
theorem knowAt (B : BattPar E) (hn : 2 ≤ B.n) (hZ : B.Z.OK) (Ex : ExtSpec) (M Wp Kc : Type)
    (A0 : Rels Kc B.St Ex (M × Wp)) (msg : M → B.J → E) :
    KnowAt (R B Ex) (B.baseIn Ex A0 fun w => msg w.1) (B.baseOut Ex A0 fun w => msg w.1)
      (fun _ _ _ wp => wp) (eps B Ex) := by
  obtain ⟨hV, hD, hI⟩ := batt_ok E B hn
  refine knowAt_seq
    (knowAt_draw B.nx _ (B.par.baseIn (A0.keepX B.Z.D) fun w => msg w.1) B.Z.err
      (fun _ _ _ h => h) ?_)
    (short_knowAtC B.par (F₁ B) Ex hV hD hI M Wp Kc (A0.keepX B.Z.D) msg)
  intro x y m _
  by_cases hx : B.InHolds x (msg m)
  · refine le_trans (le_of_eq (cnt_false fun β hβ => ?_)) (Nat.zero_le _)
    obtain ⟨wp, h1, h2⟩ := hβ
    exact h2 ⟨h1.1, hx⟩
  · refine le_trans (cnt_mono fun β hβ => ?_) (batt_cnt E B hZ x (msg m) hx)
    obtain ⟨wp, h1, -⟩ := hβ
    exact h1.2

/-- The statement holds under the two conditions. -/
theorem hAt (B : BattPar E) (hn : 2 ≤ B.n) (hZ : B.Z.OK) : HAt B :=
  fun Ex M Wp Kc A0 msg m => (knowAt B hn hZ Ex M Wp Kc A0 msg).know m

/-! ### beside the statement -/

/-- The oracles are only copied. -/
theorem copies (B : BattPar E) (Ex : ExtSpec) : (R B Ex).OnlyCopies :=
  (OnlyCopies.draw _ _ _).seq
    ⟨fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => ⟨rfl, rfl⟩⟩

/-- The state is handed on. -/
theorem passes (B : BattPar E) (Ex : ExtSpec) :
    (R B Ex).Passes Prod.snd (fun z : B.par.Mid => z.st.1) :=
  Passes.seq (r₂ := fun x : E × B.par.St => x.2.1)
    (Passes.draw B.Z.D B.nx Ex _ _ fun _ _ => rfl)
    (fun x _ _ z h => congrArg Prod.fst (B.par.outC_st x _ z h))

/-- The verifier rejects nothing. -/
theorem never_rejects (B : BattPar E) (hn : 1 ≤ B.n) (Ex : ExtSpec) (x : (B.Q → E) × B.St)
    (y : Ex.Str) (τ : Tr (R B Ex).shape) : ((R B Ex).out x y τ).isSome := by
  show ((some (B.nx x (drawn (Tr.fst τ)))).bind fun x₂ =>
    (shortRC B.par (F₁ B) Ex).out x₂ y (Tr.snd (s := [drawRound B.Z.D]) τ)).isSome
  rw [Option.bind_some, short_outC B.par (F₁ B) Ex (F₁_ok B hn)]
  rfl

private theorem errList_toList : ∀ {s : Shape} (ε : Err s), errList ε = ε.toList
  | [], _ => rfl
  | _ :: _, (e, ε) => congrArg (List.cons e) (errList_toList ε)

omit [Fintype E] in
private theorem sRounds_vals :
    ∀ l : List (PFmt E), Shape.chalList (sRounds l) = l.map fun f => Fintype.card f.Ch
  | [] => rfl
  | f :: l => congrArg (List.cons (Fintype.card f.Ch)) (sRounds_vals l)

theorem errs (B : BattPar E) (Ex : ExtSpec) :
    (eps B Ex).toList = B.Z.err :: 1 :: List.replicate B.k B.n := by
  show (Err.app (Nums.draw Unit B.Z.D B.nx Ex B.Z.err).err (shortEC B.par Ex)).toList = _
  rw [Err.toList_app, ← errList_toList (shortEC B.par Ex), shortEC_nums]
  show [B.Z.err] ++ 1 :: (List.replicate B.k (pfCube E B.n)).map PFmt.n = _
  rw [List.map_replicate]
  rfl

theorem vals (B : BattPar E) (Ex : ExtSpec) :
    (R B Ex).shape.chalList =
      Fintype.card B.Z.D :: Fintype.card E :: List.replicate B.k (Fintype.card E) := by
  show Shape.chalList ([drawRound B.Z.D] ++ (pRound0 E :: sRounds B.par.fmt)) = _
  rw [Shape.chalList_append]
  show [Fintype.card B.Z.D] ++ Fintype.card E :: Shape.chalList (sRounds B.par.fmt) = _
  rw [sRounds_vals]
  show _ ++ _ :: (List.replicate B.k (pfCube E B.n)).map (fun f => Fintype.card f.Ch) = _
  rw [List.map_replicate]
  rfl

theorem rounds (B : BattPar E) (Ex : ExtSpec) : (R B Ex).shape.chalList.length = B.k + 2 := by
  rw [vals]
  simp

end Cb.Pv.BattShort

#print axioms Cb.Pv.BattShort.F₁_ok
#print axioms Cb.Pv.BattShort.hAt
#print axioms Cb.Pv.BattShort.never_rejects
#print axioms Cb.Pv.BattShort.errs
#print axioms Cb.Pv.BattShort.vals
