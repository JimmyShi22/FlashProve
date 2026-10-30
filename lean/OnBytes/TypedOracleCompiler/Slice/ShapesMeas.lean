-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/ShapesMeas.lean: a yes of the verifier on bytes is a measurable set of oracles.

In this file "the commitment ID" ("the ID"), where it stands by itself, is not the format's. It is
the hash function's answer at a shorter string, the format's string for its ID without the record's
seed (`idCode`, OnBytes/Tie/IdKey.lean). The format's rule (R4.11; `Fmt.publishedBytes`,
Fmt/Rules4.lean) hashes the string with the seed.

`Three.VerifyB H id d` (OnBytes/TypedOracleCompiler/Slice/Shapes.lean) hangs on H through its values at the public
strings (which pick the parts), three checkers' runs, their logs, the ID's string and two keys'
records. This file shows that the oracles under which it says yes are a measurable set, if every
property of a key's record under the oracle is one (the clause `measR` of `Three.Laws`).

Main theorems.
 `measurableSet_dep` general: a set of oracles that is picked by an algorithm's value is measurable
     if each of the sets picked among is.
 `askL`, `askL_det`, `askL_toList` an algorithm that asks the strings of a finite set has, as its
     value, the oracle's own values cut to the set.
 `Three.measurableSet_accepts`, `measurableSet_clashB` at fixed tables.
 `Three.measurableSet_verifyB`.

No probability. Nothing is shown of any part.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.Shapes

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Rom Prob MeasureTheory

/-- A set of oracles that is picked by an algorithm's value: if each Q a is measurable, so is
the set of the oracles g that lie in Q at the value, under g, of the run in which every coin yields
0. -/
theorem measurableSet_dep {S : OSpec} {γ : Type} (c : OComp S γ) (Q : γ → Set (Fam S))
    (hQ : ∀ a, MeasurableSet (Q a)) : MeasurableSet {g : Fam S | g ∈ Q (c.det g)} := by
  induction c with
  | pure a => exact hQ a
  | query o q k ih =>
    have e : {g : Fam S | g ∈ Q ((OComp.query o q k).det g)} =
        ⋃ r : S.Rng o, ({g : Fam S | g o q = r} ∩ {g : Fam S | g ∈ Q ((k r).det g)}) := by
      ext g
      simp [OComp.det]
    rw [e]
    refine MeasurableSet.iUnion fun r => MeasurableSet.inter ?_ (ih r)
    have hev : Measurable fun g : Fam S => g o q :=
      (measurable_pi_apply q).comp (measurable_pi_apply o)
    exact hev (MeasurableSet.singleton r)
  | sample n k ih => exact ih 0

namespace Shapes

/-- Asks the strings of a list, one after the other, and returns the table that holds the answers
there and the default value elsewhere. -/
def askL : List (List Bool) → OComp (rom 256) Tab
  | [] => OComp.pure fun _ => default
  | s :: l => OComp.query (S := rom 256) () s fun r =>
      (askL l).bind fun T => OComp.pure fun x => if x = s then r else T x

/-- Its value under H: H's own values at the strings of the list. -/
theorem askL_det (H : Fam (rom 256)) : ∀ l : List (List Bool),
    (askL l).det H = fun x => if x ∈ l then own H x else default
  | [] => by
    funext x
    simp [askL, OComp.det]
  | s :: l => by
    show ((askL l).bind fun T => OComp.pure fun x => if x = s then own H s else T x).det H = _
    rw [OComp.det_bind, askL_det H l]
    funext x
    show (if x = s then own H s else if x ∈ l then own H x else default) = _
    by_cases hx : x = s
    · rw [if_pos hx, if_pos (by rw [hx]; exact List.mem_cons_self), hx]
    · by_cases hl : x ∈ l
      · rw [if_neg hx, if_pos hl, if_pos (List.mem_cons_of_mem _ hl)]
      · rw [if_neg hx, if_neg hl, if_neg (by
          intro h
          rcases List.mem_cons.1 h with h | h
          · exact hx h
          · exact hl h)]

/-- At the list of a finite set: the oracle's own values, cut to the set. -/
theorem askL_toList (H : Fam (rom 256)) (S : Finset (List Bool)) :
    (askL S.toList).det H = cutT S (own H) := by
  rw [askL_det]
  funext x
  unfold cutT
  by_cases hx : x ∈ S
  · rw [if_pos (Finset.mem_toList.2 hx), if_pos hx]
  · rw [if_neg (fun h => hx (Finset.mem_toList.1 h)), if_neg hx]

variable {D : DecR} {Xi : Type}

namespace Three
variable (Θ : Three D Xi)

/-- What a yes asks of three values of the checkers: the roots, the records, the instance. -/
def Rest (T₀ T₁ : Tab) (d : Files) (oK : (Θ.K T₀ T₁).Out) (oE : (Θ.E T₀ T₁).Out)
    (oF : (Θ.F T₀ T₁).Out) (g : Fam (rom 256)) : Prop :=
  (Θ.K T₀ T₁).roots oK = [Run.bytesToDig (Θ.key T₀ T₁ d).2.2.root] ∧
  (Θ.E T₀ T₁).roots oE = [Run.bytesToDig (Θ.key T₀ T₁ d).2.2.root,
    Run.bytesToDig (Θ.keyC T₀ T₁ d).2.2.root] ∧
  (Θ.F T₀ T₁).roots oF = [Run.bytesToDig (Θ.keyC T₀ T₁ d).2.2.root] ∧
  Θ.recU g (Θ.key T₀ T₁ d) = some (Θ.recK T₀ T₁ oK) ∧
  Θ.recU g (Θ.key T₀ T₁ d) = some (Θ.recE₀ T₀ T₁ oE) ∧
  Θ.recU g (Θ.keyC T₀ T₁ d) = some (Θ.recE₁ T₀ T₁ oE) ∧
  Θ.recU g (Θ.keyC T₀ T₁ d) = some (Θ.recF T₀ T₁ oF) ∧
  Θ.xOf T₀ T₁ oF = Θ.xReq d

/-- The oracles under which three values of the checkers are such that `Rest` holds of them. -/
def Q3 (T₀ T₁ : Tab) (d : Files)
    (z : Option (Θ.K T₀ T₁).Out × Option (Θ.E T₀ T₁).Out × Option (Θ.F T₀ T₁).Out) :
    Set (Fam (rom 256)) :=
  {g | ∃ oK oE oF, z.1 = some oK ∧ z.2.1 = some oE ∧ z.2.2 = some oF ∧
    Θ.Rest T₀ T₁ d oK oE oF g}

/-- The three checkers, one after the other. -/
def chk3 (T₀ T₁ : Tab) (d : Files) : OComp (rom 256)
    (Option (Θ.K T₀ T₁).Out × Option (Θ.E T₀ T₁).Out × Option (Θ.F T₀ T₁).Out) :=
  ((Θ.K T₀ T₁).chk d).bind fun a => ((Θ.E T₀ T₁).chk d).bind fun b =>
    ((Θ.F T₀ T₁).chk d).bind fun c => OComp.pure (a, b, c)

/-- Their three values. -/
theorem chk3_det (T₀ T₁ : Tab) (d : Files) (g : Fam (rom 256)) :
    (Θ.chk3 T₀ T₁ d).det g = (((Θ.K T₀ T₁).chk d).det g, ((Θ.E T₀ T₁).chk d).det g,
      ((Θ.F T₀ T₁).chk d).det g) := by
  unfold chk3
  rw [OComp.det_bind, OComp.det_bind, OComp.det_bind]
  rfl

variable (hR : ∀ k (Q : D.Rec → Prop), MeasurableSet {g | ∃ rec, Θ.recU g k = some rec ∧ Q rec})
include hR

/-- That a key's record under the oracle is a given one is a measurable set of oracles. -/
theorem measurableSet_recU (k : OnBytes.Tie.IdKey) (r : D.Rec) :
    MeasurableSet {g | Θ.recU g k = some r} := by
  have e : {g | Θ.recU g k = some r} = {g | ∃ rec, Θ.recU g k = some rec ∧ rec = r} := by
    ext g
    constructor
    · intro h
      exact ⟨r, h, rfl⟩
    · rintro ⟨rec, h, rfl⟩
      exact h
  rw [e]
  exact hR k _

/-- So is `Rest` at three given values. -/
theorem measurableSet_rest (T₀ T₁ : Tab) (d : Files) (oK : (Θ.K T₀ T₁).Out)
    (oE : (Θ.E T₀ T₁).Out) (oF : (Θ.F T₀ T₁).Out) :
    MeasurableSet {g | Θ.Rest T₀ T₁ d oK oE oF g} :=
  (MeasurableSet.const _).inter ((MeasurableSet.const _).inter ((MeasurableSet.const _).inter
    ((Θ.measurableSet_recU hR _ _).inter ((Θ.measurableSet_recU hR _ _).inter
      ((Θ.measurableSet_recU hR _ _).inter ((Θ.measurableSet_recU hR _ _).inter
        (MeasurableSet.const _)))))))

/-- `Accepts` at fixed tables is a measurable set of oracles. -/
theorem measurableSet_accepts (T₀ T₁ : Tab) (id : ZKCP.Digest 256) (d : Files) :
    MeasurableSet {g | Θ.Accepts T₀ T₁ g g id d} := by
  have hev : ∀ s : List Bool, MeasurableSet {g : Fam (rom 256) | g () s = id} := fun s =>
    measurableSet_det (OComp.query (S := rom 256) () s fun r => OComp.pure r) {r | r = id}
  have h1 : MeasurableSet {g : Fam (rom 256) |
      ∃ s, OnBytes.Tie.idCode (Θ.key T₀ T₁ d) = some s ∧ g () s = id} := by
    have key : ∀ o, OnBytes.Tie.idCode (Θ.key T₀ T₁ d) = o → MeasurableSet {g : Fam (rom 256) |
        ∃ s, OnBytes.Tie.idCode (Θ.key T₀ T₁ d) = some s ∧ g () s = id} := by
      intro o ho
      cases o with
      | none =>
        have e : {g : Fam (rom 256) |
            ∃ s, OnBytes.Tie.idCode (Θ.key T₀ T₁ d) = some s ∧ g () s = id} = ∅ := by
          ext g
          simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
          rintro ⟨s, hs, -⟩
          rw [ho] at hs
          cases hs
        rw [e]
        exact MeasurableSet.empty
      | some s =>
        have e : {g : Fam (rom 256) |
            ∃ s, OnBytes.Tie.idCode (Θ.key T₀ T₁ d) = some s ∧ g () s = id} =
            {g | g () s = id} := by
          ext g
          constructor
          · rintro ⟨s', hs, hg⟩
            rw [ho] at hs
            cases hs
            exact hg
          · intro hg
            exact ⟨s, ho, hg⟩
        rw [e]
        exact hev s
    exact key _ rfl
  have h2 : MeasurableSet {g | g ∈ Θ.Q3 T₀ T₁ d ((Θ.chk3 T₀ T₁ d).det g)} := by
    refine measurableSet_dep (Θ.chk3 T₀ T₁ d) (Θ.Q3 T₀ T₁ d) fun z => ?_
    obtain ⟨a, b, c⟩ := z
    unfold Q3
    cases a with
    | none =>
      refine (congrArg MeasurableSet ?_).mp MeasurableSet.empty
      ext g
      simp
    | some oK =>
      cases b with
      | none =>
        refine (congrArg MeasurableSet ?_).mp MeasurableSet.empty
        ext g
        simp
      | some oE =>
        cases c with
        | none =>
          refine (congrArg MeasurableSet ?_).mp MeasurableSet.empty
          ext g
          simp
        | some oF =>
          refine (congrArg MeasurableSet ?_).mp (Θ.measurableSet_rest hR T₀ T₁ d oK oE oF)
          ext g
          constructor
          · intro h
            exact ⟨oK, oE, oF, rfl, rfl, rfl, h⟩
          · rintro ⟨oK', oE', oF', h1, h2, h3, h⟩
            cases h1
            cases h2
            cases h3
            exact h
  refine (congrArg MeasurableSet ?_).mp (h1.inter h2)
  ext g
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, chk3_det, Q3]
  rfl

omit hR in
/-- A clash in the checkers' logs, at fixed tables, is a measurable set of oracles. -/
theorem measurableSet_clashB (T₀ T₁ : Tab) (d : Files) :
    MeasurableSet {g | Θ.ClashB T₀ T₁ g d} :=
  (measurableSet_det ((Θ.K T₀ T₁).chk d).withTrace {z | ¬ NoClash z.2}).union
    ((measurableSet_det ((Θ.E T₀ T₁).chk d).withTrace {z | ¬ NoClash z.2}).union
      (measurableSet_det ((Θ.F T₀ T₁).chk d).withTrace {z | ¬ NoClash z.2}))

/-- A yes of the verifier on bytes is a measurable set of oracles. It hangs on the oracle
through its values at the public strings, three runs, the ID's string and two keys' records. -/
theorem measurableSet_verifyB (id : ZKCP.Digest 256) (d : Files) :
    MeasurableSet {g | Θ.VerifyB g id d = true} := by
  have e : {g | Θ.VerifyB g id d = true} = {g | Θ.Accepts (Θ.pub₀ g) (Θ.pub₁ g) g g id d ∨
      Θ.ClashB (Θ.pub₀ g) (Θ.pub₁ g) g d} := by
    ext g
    exact Θ.verifyB_iff g id d
  rw [e]
  have h := measurableSet_dep (askL Θ.S₀.toList)
    (fun T₀ => {g | Θ.Accepts T₀ (cutT (Θ.S₁ T₀) (own g)) g g id d ∨
      Θ.ClashB T₀ (cutT (Θ.S₁ T₀) (own g)) g d}) (fun T₀ => by
      have h' := measurableSet_dep (askL (Θ.S₁ T₀).toList)
        (fun T₁ => {g | Θ.Accepts T₀ T₁ g g id d ∨ Θ.ClashB T₀ T₁ g d})
        (fun T₁ => (Θ.measurableSet_accepts hR T₀ T₁ id d).union
          (Θ.measurableSet_clashB T₀ T₁ d))
      simp only [askL_toList] at h'
      exact h')
  simp only [askL_toList] at h
  exact h

end Three

end Shapes

end OnBytes.Slice
