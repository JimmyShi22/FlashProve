-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Shape/Walk.lean: conditional, from a return: the shape of the
ledger behind a lookup's hearing is `lookUpd` (Honest/K3/Shape/Ops.lean) of the shape in front: all
thirteen components in one equation. Theorems; one definition (`Went`: what each routine's theorem
says).

Terms. Honest/K3/GLOSSARY.md: see there ledger, slot, hearing, sumcheck, face and shape (of the
ledger). In this file: the shape of the ledger is `ledSh F` (`LedSh`,
Johnson/Desc/First/Shape/Parts.lean): it holds no field element: counts, sizes, marks. `Sized F`
says that the ledger's three arrays have their size.

What is shown.
  `hearV_sh`: Sized F → hearV f F rs = some (g, G) → Sized G ∧ ledSh G = lookUpd f (ledSh F).
  `hearVia_sh`: the same of the seated hearing, at the face of the shape that the parameters make.
What stays (the number of slots, the three sizes, the arrays, the plan's number of claims, the
claims added, the two flags, the weights handed out) and what changes (the count of slots, the
marks, the owed claims) come out of the one equation.

Hypotheses that remain.
  `h`, `hv`: the return.
  `hS`: `Sized F`.
  `hs`: (in `hearVia_sh`) the parameters make the shape h.
In the routines' theorems: `e`: the routine returns (in `owe_went`, `drawV_same`, `drawsV_size`,
`sumV_went`, `openV_went`). `hp`: (in `messagesV_sh`) the face has a part of keys; `hearV_sh` has
that of the hearing's own test on the face. `h'`: (in `Went.trans`) the second of the two sentences
that are joined. `hf`: (in `foldlM_went`) each step, where it returns from a ledger whose arrays
have their size, is in `Went` at the list of steps. `hz`: (in `bits_op`) the list has m entries.

How the proof goes. The walk goes through the hearing's text routine by routine
(Johnson/Desc/First/Look/Via/Rounds.lean: `drawsV`, `drawV`, `sumV`, `openV`, `tieV`, `partsV`,
`keysV`, `messagesV`; Johnson/Desc/First/ProdV/Level.lean: `level`, `turn`, `run`), one theorem a
routine: where it returns from a ledger whose arrays have their size, the ledger behind has them
too, and its shape is the routine's list of steps (Ops.lean) run on the shape in front.

Users. Honest/K3/Shape/Guards.lean [not in this library], Honest/K3/Shape/HeardWalk.lean,
Honest/K3/Shape/Window.lean, Honest/K3/Law/Thread/CallsParts.lean,
Honest/K3/Law/Thread/DigitsParts.lean and Honest/K3/Law/Thread/HeadParts.lean import this file.

Limits. All statements are implications. No statement of this file says that the hearing returns.
`lookUpd` is a fold of steps, no closed form. Nothing is said on what was heard. No instance of
these hypotheses is exhibited in this file. An instance: Honest/K3/Shape/Guards.lean
[not in this library] (by evaluation).
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Shape.Atoms
import Johnson.Desc.ProofFile.Honest.K3.HeardLaw
import Johnson.Desc.ProofFile.Honest.K3.Law.GoesOn
import Johnson.Desc.First.Look.Via.Via

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Shape
open OnBytes (E zeroE)
open OnBytes.Model (Fork Aff orderDefault)
open OnBytes.PscRun (Sized)
open VerifiableInference.Desc.First.Shape (LedSh ledSh)
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.Part.MaskedSum (Call Var ownSlots)
open VerifiableInference.Desc.K3 (HeardV hearV messagesV Hr drawsV drawV sumV openV tieV partsV
  keysV leafVars bitsCall noVar faceOf)
open VerifiableInference.Desc.First.ProdV (LevelOut level turn Carried levelVars levelEnds)
open VerifiableInference.Desc.LinkJoin.ViaL (bindHr_some)
open ProofFile.Honest.K3.Law (slot_spec must_spec drawsV_same hearV_messages)

variable {α β γ : Type}

local notation "vRun" => VerifiableInference.Desc.First.ProdV.run
local notation "KFace" => VerifiableInference.Desc.K3.Face

/-- What a routine's theorem says: the sizes are kept; the shape behind is the steps run on the
shape in front. -/
def Went (F G : Fork) (ops : List Op) : Prop := Sized G ∧ ledSh G = runOps ops (ledSh F)

theorem Went.refl {F : Fork} (hS : Sized F) : Went F F [] := ⟨hS, rfl⟩

theorem Went.trans {F G H : Fork} {a b : List Op} (h : Went F G a) (h' : Went G H b) :
    Went F H (a ++ b) := ⟨h'.1, by rw [h'.2, h.2, runOps_append]⟩

/-! ## 1 The small texts -/

theorem owe_went {w : String} {F G : Fork} {rs rest : List Fmt.RoundView} {n : Nat} (hS : Sized F)
    (e : Hr.owe w F rs = some (n, G, rest)) : Went F G [.owe] := by
  have e' : some ((F.owe w).1, (F.owe w).2, rs) = some (n, G, rest) := e
  cases e'
  exact ⟨hS, owe_sh F w⟩

theorem drawV_same {F G : Fork} {rs rest : List Fmt.RoundView} {a : E}
    (e : drawV F rs = some (a, G, rest)) : G = F := by
  unfold drawV at e
  split at e
  · rename_i x G' rest' hx
    split at e
    · obtain rfl : G' = G := congrArg (·.2.1) (Option.some.inj e)
      exact drawsV_same hx
    · exact nomatch e
  · exact nomatch e

/-- A round of samples hands out just n elements. -/
theorem drawsV_size {n : Nat} {F G : Fork} {rs rest : List Fmt.RoundView} {a : Array E}
    (e : drawsV n F rs = some (a, G, rest)) : a.size = n := by
  unfold drawsV at e
  cases rs with
  | nil => exact nomatch e
  | cons r rs' =>
    dsimp only at e
    split at e
    · obtain ⟨x, hx, e⟩ := Option.map_eq_some_iff.1 e
      obtain ⟨s, d⟩ := x
      obtain ⟨_, _, h3, h4⟩ := MaskedSum.roundOf_spec hx
      have ea : d.toArray = a := congrArg (·.1) e
      rw [← ea, List.size_toArray, h4, List.length_map, h3]
    · exact nomatch e

/-! ## 2 The masked sumcheck; the product levels -/

theorem sumV_went {C : Aff} {k : Call} {endTerm : List E → List E → E} {F G : Fork}
    {rs rest : List Fmt.RoundView} {a : MaskedSum.Heard × Aff} (hS : Sized F)
    (e : sumV C k endTerm F rs = some (a, G, rest)) : Went F G [sumOp k] := by
  unfold sumV at e
  split at e
  · exact nomatch e
  · split at e
    · rename_i h row G' hw
      split at e
      · exact nomatch e
      · obtain rfl : G' = G := congrArg (·.2.1) (Option.some.inj e)
        exact whole_sh hS hw
    · exact nomatch e

theorem openV_went {C : Aff} {vs : List Var} {F G : Fork} {rs rest : List Fmt.RoundView}
    {a : MaskedSum.Heard} (hS : Sized F) (e : openV C vs F rs = some (a, G, rest)) :
    Went F G [.left (ownSlots vs)] := by
  unfold openV at e
  split at e
  · exact nomatch e
  · obtain ⟨x, hx, e⟩ := Option.map_eq_some_iff.1 e
    obtain ⟨h, G'⟩ := x
    obtain rfl : G' = G := congrArg (·.2.1) e
    exact left_sh hS hx

/-- A level's step does not depend on the level's point. -/
theorem levelOp_eq (m : Nat) (z : Array E) (order : List Nat) :
    sumOp { lead := 0, vs := levelVars m z order, ends := some levelEnds } = levelOp order := by
  unfold levelOp sumOp
  rw [ownSlots_blind
    (vs := Call.all { lead := 0, vs := levelVars m z order, ends := some levelEnds })
    (ws := Call.all { lead := 0, vs := levelVars 0 #[] order, ends := some levelEnds })
    (by simp [Call.all, levelVars, Function.comp_def, Var.d])]
  rfl

theorem level_went {m : Nat} {z : Array E} {order : List Nat} {C : Aff} {F G : Fork}
    {rs rest : List Fmt.RoundView} {o : LevelOut} (hS : Sized F)
    (h : level m z order C F rs = some (o, G, rest)) : Went F G [levelOp order] := by
  unfold level at h
  split at h
  · exact nomatch h
  · split at h
    · rename_i hd row G' line rest' hw _
      split at h
      · split at h
        · exact nomatch h
        · obtain rfl : G' = G := congrArg (·.2.1) (Option.some.inj h)
          rw [← levelOp_eq m z order]
          exact whole_sh hS hw
      · exact nomatch h
    · exact nomatch h

theorem turn_went {order : List Nat} {s s' : Carried} {m : Nat} {F G : Fork}
    {rs rest : List Fmt.RoundView} (hS : Sized F) (h : turn order s m F rs = some (s', G, rest)) :
    Went F G [levelOp order] := by
  unfold turn at h
  obtain ⟨x, hx, e⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨o, G', rest'⟩ := x
  obtain rfl : G' = G := congrArg (·.2.1) e
  exact level_went hS hx

theorem fold_went (m0 : Nat) (orders : Nat → List Nat) : ∀ (l : List Nat)
    (x y : Carried × Fork × List Fmt.RoundView), Sized x.2.1 →
    l.foldlM (fun (x : Carried × Fork × List Fmt.RoundView) i =>
      turn (orders (m0 + i)) x.1 (m0 + i) x.2.1 x.2.2) x = some y →
    Went x.2.1 y.2.1 (levelOps m0 orders l)
  | [], x, y, hS, h => by
    obtain rfl : x = y := Option.some.inj h
    exact Went.refl hS
  | i :: l, x, y, hS, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨z, hz, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨s', G, rest⟩ := z
    have w1 := turn_went hS hz
    exact w1.trans (fold_went m0 orders l _ y w1.1 h)

theorem run_went {m0 n : Nat} {orders : Nat → List Nat} {s s' : Carried} {F G : Fork}
    {rs rest : List Fmt.RoundView} (hS : Sized F) (h : vRun m0 n orders s F rs = some (s', G, rest)) :
    Went F G (levelOps m0 orders (List.range n)) :=
  fold_went m0 orders _ (s, F, rs) (s', G, rest) hS h

/-! ## 3 The tie, the parts' roots, the key trees -/

theorem foldlM_went {f : β → γ → Hr β} {op : List Op}
    (hf : ∀ (s : β) (a : γ) (F G : Fork) (rs rest : List Fmt.RoundView) (b : β), Sized F →
      f s a F rs = some (b, G, rest) → Went F G op) :
    ∀ (l : List γ) (s : β) (F G : Fork) (rs rest : List Fmt.RoundView) (b : β), Sized F →
      (l.foldlM f s) F rs = some (b, G, rest) → Went F G (l.flatMap fun _ => op)
  | [], s, F, G, rs, rest, b, hS, h => by
    have h' : (pure s : Hr β) F rs = some (b, G, rest) := h
    rw [(pure_spec h').2.1]
    exact Went.refl hS
  | a :: l, s, F, G, rs, rest, b, hS, h => by
    have h' : (f s a >>= fun s' => l.foldlM f s') F rs = some (b, G, rest) := h
    obtain ⟨s', F1, r1, e1, h2⟩ := bindHr_some h'
    have w1 := hf s a F F1 rs r1 s' hS e1
    exact w1.trans (foldlM_went hf l s' F1 G r1 rest b w1.1 h2)

theorem tieV_went {w : Nat} {a : E} {F G : Fork} {rs rest : List Fmt.RoundView}
    {x : Array Aff × Nat × Array Nat} (hS : Sized F) (h : tieV w a F rs = some (x, G, rest)) :
    Went F G (tieOps w) := by
  unfold tieV at h
  try dsimp only at h
  obtain ⟨y, F1, r1, e1, h⟩ := bindHr_some h
  obtain ⟨s, F2, r2, e2, h⟩ := bindHr_some h
  have w1 := sumV_went hS e1
  have w2 := foldlM_went (op := [sumOp (noVar 3 2)])
    (fun s _ F G rs rest b hS e => by
      obtain ⟨y, F1, r1, e1, e⟩ := bindHr_some e
      rw [(pure_spec e).2.1]
      exact sumV_went hS e1) _ _ _ _ _ _ _ w1.1 e2
  rw [(pure_spec h).2.1]
  exact w1.trans w2

theorem partsV_went : ∀ (n : Nat) (rows : Array Aff) (C : Aff) (F G : Fork)
    (rs rest : List Fmt.RoundView) (x : Array Aff × List Aff), Sized F →
    partsV n rows C F rs = some (x, G, rest) → Went F G (partsOps n) ∧ x.2.length = n + 1
  | 0, rows, C, F, G, rs, rest, x, hS, h => by
    unfold partsV at h
    obtain ⟨a, b, _⟩ := pure_spec h
    rw [a, b]
    exact ⟨Went.refl hS, rfl⟩
  | n + 1, rows, C, F, G, rs, rest, x, hS, h => by
    unfold partsV at h
    obtain ⟨w, F1, r1, e1, h⟩ := bindHr_some h
    obtain ⟨y, F2, r2, e2, h⟩ := bindHr_some h
    obtain ⟨a, b, _⟩ := pure_spec h
    have w1 := sumV_went hS e1
    obtain ⟨w2, l2⟩ := partsV_went n _ _ F1 F2 r1 r2 y w1.1 e2
    rw [a, b]
    exact ⟨w1.trans w2, by show y.2.length + 1 = n + 1 + 1; rw [l2]⟩

theorem keysV_went (f : KFace) : ∀ (xs : List (Nat × Nat)) (Cs : List Aff) (rows : Array Aff)
    (F G : Fork) (rs rest : List Fmt.RoundView) (x : Array Aff × List (Array E × Aff)),
    xs.length = Cs.length → Sized F → keysV f xs Cs rows F rs = some (x, G, rest) →
    Went F G (keysOps f xs)
  | [], [], rows, F, G, rs, rest, x, _, hS, h => by
    unfold keysV at h
    rw [(pure_spec h).2.1]
    exact Went.refl hS
  | [], _ :: _, _, _, _, _, _, _, hl, _, _ => nomatch hl
  | _ :: _, [], _, _, _, _, _, _, hl, _, _ => nomatch hl
  | y :: xs, C :: Cs, rows, F, G, rs, rest, x, hl, hS, h => by
    unfold keysV at h
    obtain ⟨k, F1, r1, e1, h⟩ := bindHr_some h
    obtain ⟨z, F2, r2, e2, h⟩ := bindHr_some h
    have w1 : Went F F1 (levelOps 0 (f.orders y.2) (List.range y.1)) := run_went hS e1
    have w2 := keysV_went f xs Cs _ F1 F2 r1 r2 z (Nat.succ.inj hl) w1.1 e2
    rw [(pure_spec h).2.1]
    exact w1.trans w2

/-! ## 4 The lookup's rounds -/

/-- The leaves' own slots do not depend on the point. -/
theorem leaf_own (f : KFace) (z : Array E) : ownSlots (leafVars f z) = ownSlots (leafVars f #[]) :=
  ownSlots_blind (by simp [leafVars, Function.comp_def, Var.d])

/-- The bits' step depends on the number of the point's coordinates alone. -/
theorem bits_op (z : List E) (m : Nat) (hz : z.length = m) :
    sumOp (bitsCall z) = sumOp (bitsCall (List.replicate m zeroE)) := by
  subst hz
  unfold sumOp
  rw [ownSlots_blind (vs := (bitsCall z).all) (ws := (bitsCall (List.replicate z.length zeroE)).all)
    (by simp [Call.all, bitsCall, Function.comp_def, Var.d])]
  rfl

/-- A face that passes its own test has a part of keys. -/
theorem parts_pos {f : KFace} (h : f.ok = true) : 1 ≤ f.parts.length := by
  unfold VerifiableInference.Desc.K3.Face.ok at h
  simp only [Bool.and_eq_true] at h
  have hne := h.1.1.1.1.2
  cases hp : f.parts with
  | nil =>
    rw [hp] at hne
    exact absurd hne (by decide)
  | cons a l => exact Nat.succ_le_succ (Nat.zero_le _)

/-- **The lookup's rounds, heard in order.** Conditional on the return, on `Sized` in front, and on
the face having a part of keys. -/
theorem messagesV_sh {f : KFace} {F G : Fork} {rs rest : List Fmt.RoundView} {g : HeardV} (hS : Sized F)
    (hp : 1 ≤ f.parts.length) (h : messagesV f F rs = some (g, G, rest)) :
    Went F G (lookOps f) := by
  unfold messagesV at h
  obtain ⟨slot0, F1, r1, e1, h⟩ := bindHr_some h
  obtain ⟨o1, F2, r2, e2, h⟩ := bindHr_some h
  obtain ⟨o2, F3, r3, e3, h⟩ := bindHr_some h
  obtain ⟨o3, F4, r4, e4, h⟩ := bindHr_some h
  dsimp only at h
  obtain ⟨theta, F5, r5, e5, h⟩ := ite_bind_some h
  obtain ⟨alpha, F6, r6, e6, h⟩ := bindHr_some h
  obtain ⟨⟨rows, sZ, sG⟩, F7, r7, e7, h⟩ := bindHr_some h
  obtain ⟨⟨rows2, roots⟩, F8, r8, e8, h⟩ := bindHr_some h
  obtain ⟨jo, F9, r9, e9, h⟩ := bindHr_some h
  obtain ⟨⟨rows3, keys⟩, F10, r10, e10, h⟩ := bindHr_some h
  obtain ⟨u1, F11, r11, e11, h⟩ := bindHr_some h
  obtain ⟨table, F12, r12, e12, h⟩ := bindHr_some h
  obtain ⟨u2, F13, r13, e13, h⟩ := bindHr_some h
  obtain ⟨leaves, F14, r14, e14, h⟩ := bindHr_some h
  obtain ⟨ze, F15, r15, e15, h⟩ := bindHr_some h
  obtain ⟨bits, F16, r16, e16, h⟩ := bindHr_some h
  obtain ⟨sl, F17, r17, e17, h⟩ := bindHr_some h
  obtain ⟨u3, F18, r18, e18, h⟩ := bindHr_some h
  rw [(slot_spec e1).2] at e2
  have w2 := owe_went hS e2
  have w3 := owe_went w2.1 e3
  have w4 := owe_went w3.1 e4
  have q5 : F5 = F4 := by
    split at e5
    · exact drawV_same e5
    · exact (pure_spec e5).2.1
  rw [drawV_same e6, q5] at e7
  have w7 := tieV_went w4.1 e7
  obtain ⟨w8, l8⟩ := partsV_went _ _ _ _ _ _ _ _ w7.1 e8
  rw [drawsV_same e9] at e10
  have hok : f.parts.zipIdx.length = roots.length := by
    have l8' : roots.length = f.parts.length - 1 + 1 := l8
    rw [List.length_zipIdx, l8']
    omega
  have w10 := keysV_went f _ _ _ _ _ _ _ _ hok w8.1 e10
  rw [(must_spec e11).2] at e12
  have w12 := run_went w10.1 e12
  rw [(must_spec e13).2] at e14
  have w14 := openV_went w12.1 e14
  rw [leaf_own] at w14
  rw [drawsV_same e15] at e16
  have w16 := sumV_went w14.1 e16
  rw [bits_op _ (f.mu + f.d) (by simp [drawsV_size e15])] at w16
  have qG : G = F16 := by
    rw [(pure_spec h).2.1, (must_spec e18).2, (slot_spec e17).2]
  rw [qG]
  exact w2.trans (w3.trans (w4.trans (w7.trans (w8.trans (w10.trans (w12.trans
    (w14.trans w16)))))))

/-! ## 5 The tops -/

/-- **The shape of the ledger behind a lookup's hearing.** Conditional on the return and on `Sized`
in front. No instance of these hypotheses is exhibited in this file. -/
theorem hearV_sh {f : KFace} {F G : Fork} {rs : List Fmt.RoundView} {g : HeardV} (hS : Sized F)
    (h : hearV f F rs = some (g, G)) : Sized G ∧ ledSh G = lookUpd f (ledSh F) := by
  obtain ⟨hok, hm⟩ := hearV_messages h
  exact messagesV_sh hS (parts_pos hok) hm

/-- **The same of the seated hearing.** Conditional on the parameters making the shape h, the
return, and `Sized` in front. No instance of these hypotheses is exhibited in this file. -/
theorem hearVia_sh {p : VerifiableInference.Desc.First.Look.P} {h : OnBytes.Model.Forest.Shape}
    {F G : Fork} {rs : List Fmt.RoundView} {H : OnBytes.Model.Forest.Heard} (hS : Sized F)
    (hs : p.shape = some h)
    (hv : VerifiableInference.Desc.K3.Law.hearVia p F rs = some (H, G)) :
    Sized G ∧ ledSh G = lookUpd (faceOf h) (ledSh F) := by
  unfold VerifiableInference.Desc.K3.Law.hearVia at hv
  split at hv
  · rename_i h' hs'
    obtain rfl : h' = h := Option.some.inj (hs'.symm.trans hs)
    split at hv
    · obtain ⟨x, hx, hv⟩ := Option.bind_eq_some_iff.1 hv
      obtain ⟨g', _, e⟩ := Option.map_eq_some_iff.1 hv
      obtain ⟨gv, G'⟩ := x
      obtain rfl : G' = G := congrArg (·.2) e
      exact hearV_sh hS hx
    · exact nomatch hv
  · exact nomatch hv

end ProofFile.Honest.K3.Shape

#print axioms ProofFile.Honest.K3.Shape.Went.refl
#print axioms ProofFile.Honest.K3.Shape.Went.trans
#print axioms ProofFile.Honest.K3.Shape.owe_went
#print axioms ProofFile.Honest.K3.Shape.drawV_same
#print axioms ProofFile.Honest.K3.Shape.drawsV_size
#print axioms ProofFile.Honest.K3.Shape.sumV_went
#print axioms ProofFile.Honest.K3.Shape.openV_went
#print axioms ProofFile.Honest.K3.Shape.levelOp_eq
#print axioms ProofFile.Honest.K3.Shape.level_went
#print axioms ProofFile.Honest.K3.Shape.turn_went
#print axioms ProofFile.Honest.K3.Shape.fold_went
#print axioms ProofFile.Honest.K3.Shape.run_went
#print axioms ProofFile.Honest.K3.Shape.foldlM_went
#print axioms ProofFile.Honest.K3.Shape.tieV_went
#print axioms ProofFile.Honest.K3.Shape.partsV_went
#print axioms ProofFile.Honest.K3.Shape.keysV_went
#print axioms ProofFile.Honest.K3.Shape.leaf_own
#print axioms ProofFile.Honest.K3.Shape.bits_op
#print axioms ProofFile.Honest.K3.Shape.parts_pos
#print axioms ProofFile.Honest.K3.Shape.messagesV_sh
#print axioms ProofFile.Honest.K3.Shape.hearV_sh
#print axioms ProofFile.Honest.K3.Shape.hearVia_sh
