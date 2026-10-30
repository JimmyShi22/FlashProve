-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/NoDigest.lean: the honest side of the kind "lookup" (K3). The
verifier's hearing of a lookup reads no sealed digest: on rounds without their digests it returns
what it returns on the rounds themselves. For every face. Theorems, with one class (`Blind`) and its
fifteen instances, an abbreviation (`nd`), a definition (`leftNd`) and a local tactic ("blind").

Terms. Honest/K3/GLOSSARY.md ("hearing", "decision", "step").

What is shown.
  `varRounds_nd`, `readAll_nd`, `hear_nd`, `whole_nd`: the masked sumcheck's own text.
  `Blind x`: a text that hears does on rounds without digests what it does on the rounds, and leaves
    the rounds that it leaves, without digests. The class is closed under the connectives of the
    verifier's text.
  `level_nd`, `run_nd`: the grand product's texts.
  `hearV_noDigest`, `hearVia_noDigest`, `decideVia_noDigest`: the hearing; the hearing at a place;
    the decision at a place.

Hypotheses that remain. None in the theorems named above. `hx`, `hf`: (in `Blind.bind`,
`blind_foldlM`) the texts that are joined are `Blind`.

Users. A sub-protocol's step shows its `decide` the rounds without the sealed digest (`noDigest`,
Johnson/Desc/Block.lean). The theorems of this folder speak of the hearing on the rounds as they
were played. This file is imported by Honest/K3/Law/StepYes.lean and
Honest/K3/Law/Thread/MemberBack.lean.

Limits. The statements are equations between what two calls of one text return; whether a text
returns is not spoken of.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Index
import Johnson.Desc.First.Look.Via.Via

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.NoDigest
open OnBytes (E zeroE)
open OnBytes.Model (Fork Aff)
open VerifiableInference.Desc (noDigest)
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.K3 (HeardV hearV messagesV Hr drawsV drawV sumV openV tieV partsV
  keysV)
open VerifiableInference.Desc.First.ProdV (Hears LevelOut level turn Carried elementsAlone run_zero
  run_succ)

local notation "vRun" => VerifiableInference.Desc.First.ProdV.run

variable {α β γ : Type}

/-- Rounds without their sealed digests. -/
abbrev nd (rs : List Fmt.RoundView) : List Fmt.RoundView := rs.map noDigest

/-! ## The masked sumcheck's own text -/

theorem varRounds_nd : ∀ (vs : List MaskedSum.Var) (rs : List Fmt.RoundView),
    MaskedSum.varRounds vs (nd rs) = (MaskedSum.varRounds vs rs).map fun y => (y.1, nd y.2)
  | [], _ => rfl
  | _ :: _, [] => rfl
  | v :: vs, r :: rs => by
    show MaskedSum.varRounds (v :: vs) (noDigest r :: nd rs) = _
    unfold MaskedSum.varRounds
    rw [varRounds_nd vs rs, roundOf_noDigest]
    rcases MaskedSum.roundOf (v.d - 1) 1 r with _ | ⟨s, gs⟩
    · rfl
    · rcases MaskedSum.varRounds vs rs with _ | ⟨l, rest⟩
      · rcases gs with _ | ⟨g, _ | ⟨g', gs'⟩⟩ <;> rfl
      · rcases gs with _ | ⟨g, _ | ⟨g', gs'⟩⟩ <;> rfl

theorem readAll_nd (k : MaskedSum.Call) : ∀ rs : List Fmt.RoundView,
    MaskedSum.readAll k (nd rs) = MaskedSum.readAll k rs
  | [] => rfl
  | r :: rest => by
    show MaskedSum.readAll k (noDigest r :: nd rest) = _
    unfold MaskedSum.readAll
    have e : MaskedSum.firstRound k (noDigest r) = MaskedSum.firstRound k r := rfl
    simp only [e, varRounds_nd]
    rcases MaskedSum.firstRound k r with
        _ | ⟨a, _ | ⟨mu, _ | ⟨mu', b'⟩⟩, _ | ⟨eps, _ | ⟨eps', c'⟩⟩⟩ <;>
      rcases MaskedSum.varRounds k.all rest with _ | ⟨l, _ | ⟨rv, _ | ⟨rv', left'⟩⟩⟩ <;>
      rcases k.ends with _ | e' <;> rfl

theorem hear_nd (C : Aff) (k : MaskedSum.Call) (F : Fork) (rs : List Fmt.RoundView) :
    MaskedSum.hear C k F (nd rs) = MaskedSum.hear C k F rs := by
  unfold MaskedSum.hear
  rw [readAll_nd]

theorem whole_nd (C : Aff) (k : MaskedSum.Call) (endTerm : List E → List E → E) (F : Fork)
    (rs : List Fmt.RoundView) : MaskedSum.whole C k endTerm F (nd rs) = MaskedSum.whole C k endTerm F rs :=
      by
  unfold MaskedSum.whole
  rw [hear_nd]

/-! ## Texts that hear -/

/-- What a text that hears yields, with the rounds that are left shown without their digests. -/
def leftNd (y : Option (α × Fork × List Fmt.RoundView)) : Option (α × Fork × List Fmt.RoundView) :=
  y.map fun z => (z.1, z.2.1, nd z.2.2)

/-- On rounds without digests x does what it does on the rounds. -/
class Blind (x : Hr α) : Prop where
  same : ∀ (F : Fork) (rs : List Fmt.RoundView), x F (nd rs) = leftNd (x F rs)

instance blind_pure (a : α) : Blind (pure a : Hr α) := ⟨fun _ _ => rfl⟩

theorem Blind.bind {x : Hr α} {f : α → Hr β} (hx : Blind x) (hf : ∀ a, Blind (f a)) :
    Blind (x >>= f) :=
  ⟨fun F rs => by
    show Hr.andThen x f F (nd rs) = leftNd (Hr.andThen x f F rs)
    unfold Hr.andThen
    rw [hx.same]
    rcases x F rs with _ | ⟨a, G, rest⟩
    · rfl
    · exact (hf a).same G rest⟩

instance blind_bind (x : Hr α) (f : α → Hr β) [Blind x] [∀ a, Blind (f a)] : Blind (x >>= f) :=
  Blind.bind inferInstance inferInstance

instance blind_ite (p : Prop) [Decidable p] (x y : Hr α) [Blind x] [Blind y] :
    Blind (if p then x else y) := by
  split <;> infer_instance

instance blind_slot : Blind Hr.slot := ⟨fun _ _ => rfl⟩

instance blind_owe (what : String) : Blind (Hr.owe what) := ⟨fun _ _ => rfl⟩

instance blind_must (b : Bool) : Blind (Hr.must b) :=
  ⟨fun F rs => by
    unfold Hr.must
    split <;> rfl⟩

/-- Walks a do-block: bind by bind, into each `if` and each pattern. -/
local macro "blind" : tactic =>
  `(tactic| repeat' first
    | infer_instance
    | refine Blind.bind ?_ ?_
    | intro _
    | split)

theorem blind_foldlM {f : β → γ → Hr β} (hf : ∀ s a, Blind (f s a)) :
    ∀ (l : List γ) (s : β), Blind (l.foldlM f s)
  | [], s => by
    show Blind (pure s : Hr β)
    infer_instance
  | a :: l, s => by
    show Blind (f s a >>= fun s' => l.foldlM f s')
    exact Blind.bind (hf s a) fun s' => blind_foldlM hf l s'

instance blind_drawsV (n : Nat) : Blind (drawsV n) :=
  ⟨fun F rs => by
    cases rs with
    | nil => rfl
    | cons r rest =>
      show drawsV n F (noDigest r :: nd rest) = _
      unfold drawsV
      have e1' : elementsAlone [noDigest r] = elementsAlone [r] := rfl
      simp only [e1', roundOf_noDigest]
      split
      · rcases MaskedSum.roundOf 0 n r with _ | y <;> rfl
      · rfl⟩

instance blind_drawV : Blind drawV :=
  ⟨fun F rs => by
    unfold drawV
    rw [(blind_drawsV 1).same]
    rcases drawsV 1 F rs with _ | ⟨y, G, rest⟩
    · rfl
    · show (if y.size == 1 then _ else _) = leftNd (if y.size == 1 then _ else _)
      split <;> rfl⟩

instance blind_sumV (C : Aff) (k : MaskedSum.Call) (endTerm : List E → List E → E) :
    Blind (sumV C k endTerm) :=
  ⟨fun F rs => by
    unfold sumV
    rw [← List.map_take, ← List.map_drop, alone_noDigest, whole_nd]
    split
    · rfl
    · rcases MaskedSum.whole C k endTerm F (rs.take (VerifiableInference.Desc.K3.roundsOf k)) with
        _ | ⟨h, row, G⟩
      · rfl
      · show (if _ then _ else _) = leftNd (if _ then _ else _)
        split <;> rfl⟩

instance blind_openV (C : Aff) (vs : List MaskedSum.Var) : Blind (openV C vs) :=
  ⟨fun F rs => by
    unfold openV
    rw [← List.map_take, ← List.map_drop, alone_noDigest, hear_nd]
    split
    · rfl
    · rcases MaskedSum.hear C { lead := 0, vs := vs, ends := none } F (rs.take (vs.length + 1)) with
        _ | ⟨h, G⟩ <;> rfl⟩

/-! ## The grand product's texts -/

theorem level_nd (m : Nat) (z : Array E) (order : List Nat) (C : Aff) (F : Fork)
    (rs : List Fmt.RoundView) : level m z order C F (nd rs) = leftNd (level m z order C F rs) := by
  unfold level
  rw [← List.map_take, ← List.map_take, ← List.map_drop, alone_noDigest, whole_nd]
  split
  · rfl
  · rcases MaskedSum.whole C _ _ F (rs.take (m + 3)) with _ | ⟨h, row, G⟩
    · rfl
    · rcases rs.drop (m + 3) with _ | ⟨line, rest⟩
      · rfl
      · simp only [List.map_cons, roundOf_noDigest]
        rcases MaskedSum.roundOf 0 1 line with _ | ⟨s, _ | ⟨g, _ | ⟨g', gs'⟩⟩⟩
        · rfl
        · rfl
        · dsimp only
          split <;> rfl
        · rfl

theorem turn_nd (order : List Nat) (s : Carried) (m : Nat) (F : Fork) (rs : List Fmt.RoundView) :
    turn order s m F (nd rs) = leftNd (turn order s m F rs) := by
  unfold turn
  rw [level_nd]
  rcases level m s.point order s.form F rs with _ | ⟨o, G, rest⟩ <;> rfl

theorem run_nd (m0 : Nat) (orders : Nat → List Nat) (s : Carried) (F : Fork) (rs : List Fmt.RoundView) :
    ∀ n, vRun m0 n orders s F (nd rs) = leftNd (vRun m0 n orders s F rs)
  | 0 => rfl
  | n + 1 => by
    rw [run_succ, run_succ, run_nd m0 orders s F rs n]
    rcases vRun m0 n orders s F rs with _ | ⟨c, G, rest⟩
    · rfl
    · exact turn_nd _ _ _ _ _

instance blind_run (m0 n : Nat) (orders : Nat → List Nat) (s : Carried) :
    Blind (Hr.of (vRun m0 n orders s)) := ⟨fun F rs => run_nd m0 orders s F rs n⟩

/-! ## The lookup's texts -/

instance blind_tieV (w : Nat) (a : E) : Blind (tieV w a) := by
  unfold tieV
  refine Blind.bind inferInstance fun x => ?_
  refine Blind.bind (blind_foldlM (fun s _ => by blind) _ _) fun _ => ?_
  infer_instance

theorem blind_partsV : ∀ (n : Nat) (rows : Array Aff) (C : Aff), Blind (partsV n rows C)
  | 0, rows, C => by
    unfold partsV
    infer_instance
  | n + 1, rows, C => by
    unfold partsV
    refine Blind.bind inferInstance fun w => ?_
    refine Blind.bind (blind_partsV n _ _) fun _ => ?_
    infer_instance

instance (n : Nat) (rows : Array Aff) (C : Aff) : Blind (partsV n rows C) := blind_partsV n rows C

theorem blind_keysV (f : LFace) : ∀ (xs : List (Nat × Nat)) (Cs : List Aff) (rows : Array Aff),
    Blind (keysV f xs Cs rows)
  | [], _, rows => by
    unfold keysV
    infer_instance
  | _ :: _, [], rows => by
    unfold keysV
    infer_instance
  | x :: xs, C :: Cs, rows => by
    unfold keysV
    refine Blind.bind inferInstance fun k => ?_
    refine Blind.bind (blind_keysV f xs Cs _) fun _ => ?_
    infer_instance

instance (f : LFace) (xs : List (Nat × Nat)) (Cs : List Aff) (rows : Array Aff) :
    Blind (keysV f xs Cs rows) := blind_keysV f xs Cs rows

instance blind_messagesV (f : LFace) : Blind (messagesV f) := by
  unfold messagesV
  blind

/-- **The lookup's hearing reads no sealed digest.** -/
theorem hearV_noDigest (f : LFace) (F : Fork) (rs : List Fmt.RoundView) :
    hearV f F (rs.map noDigest) = hearV f F rs := by
  unfold hearV
  rw [(blind_messagesV f).same]
  split
  · rcases messagesV f F rs with _ | ⟨g, G, rest⟩
    · rfl
    · rcases rest with _ | ⟨r, rest'⟩ <;> rfl
  · rfl

/-- The hearing at a place likewise. -/
theorem hearVia_noDigest (p : VerifiableInference.Desc.First.Look.P) (F : Fork)
    (rs : List Fmt.RoundView) : VerifiableInference.Desc.K3.Law.hearVia p F (rs.map noDigest) =
      VerifiableInference.Desc.K3.Law.hearVia p F rs := by
  unfold VerifiableInference.Desc.K3.Law.hearVia
  simp only [hearV_noDigest]

/-- The decision at a place likewise. -/
theorem decideVia_noDigest {S Cl : Type} (seat : VerifiableInference.Desc.K3.Seat S Cl)
    (p : VerifiableInference.Desc.First.Look.P) (s : S) (rs : List Fmt.RoundView) :
    VerifiableInference.Desc.K3.Law.decideVia seat p s (rs.map noDigest) =
      VerifiableInference.Desc.K3.Law.decideVia seat p s rs := by
  unfold VerifiableInference.Desc.K3.Law.decideVia
  simp only [hearVia_noDigest]

#print axioms ProofFile.Honest.K3.NoDigest.Blind.bind
#print axioms ProofFile.Honest.K3.NoDigest.blind_foldlM
#print axioms ProofFile.Honest.K3.NoDigest.blind_partsV
#print axioms ProofFile.Honest.K3.NoDigest.blind_keysV
#print axioms ProofFile.Honest.K3.NoDigest.varRounds_nd
#print axioms ProofFile.Honest.K3.NoDigest.readAll_nd
#print axioms ProofFile.Honest.K3.NoDigest.hear_nd
#print axioms ProofFile.Honest.K3.NoDigest.whole_nd
#print axioms ProofFile.Honest.K3.NoDigest.level_nd
#print axioms ProofFile.Honest.K3.NoDigest.turn_nd
#print axioms ProofFile.Honest.K3.NoDigest.run_nd
#print axioms ProofFile.Honest.K3.NoDigest.hearV_noDigest
#print axioms ProofFile.Honest.K3.NoDigest.hearVia_noDigest
#print axioms ProofFile.Honest.K3.NoDigest.decideVia_noDigest

end ProofFile.Honest.K3.NoDigest
