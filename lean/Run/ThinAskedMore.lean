-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/ThinAskedMore.lean: two more facts on the queries of the evaluable form of the compiled
verifier.

The verifier is `verifyP` (Run/ThinDefs.lean; see Run/ThinAsked.lean). First: if all rounds are
local, the chain never joins. Second: where the strict format holds and the wiring lists no external
position, every leaf query is a symbol's body together with a salt of the format's length.

1. What the file contains.
   `InpOK`: A check's leaf query is (emb p a, salt) for some position p and symbol a, with
     `salt.length = sMT`.

2. What is checked when the file compiles. Nothing beyond the proofs.

3. Theorems.
   `chainP_local`: Take the annotation "all rounds local" (`allLo`, Run/TwinKit.lean) and start
     `chainP` from a phase without a slot value. Then the phase that `chainP` returns has no slot
     value. (A chain joins at the first shared round and has a slot value from then on.)
   `forestsP_inp`: `forestsP = some Fs` and the strict format of the openings (`sSP sMT`) imply that
     every check of the forests Fs is `InpOK`.
   `forestsOfP_inp`.

4. What is not claimed. Nothing on what the queries' answers are. No statement on soundness follows.

Terms: lean/GLOSSARY.md.
-/
import Run.ThinAsked
import Run.TwinKit

set_option autoImplicit false

namespace Run.Thin
open Iop Rom Compile Compile.Batch Run.Twin

section
variable {I X : Type} {lam K : ℕ} (Lf : Unit → BatchProtocol I X) (g : Fam (spec lam K (Lf ())))

/-- With local rounds alone a chain that has not joined does not join. -/
theorem chainP_local (early : X → X) (late : Option ℕ) (t : Tag) (cms : List (Dig lam))
    (x : Option X) (salt : Bits) (rtreq : Dig lam) :
    ∀ (S : List RS) (W : RoundsQueryLayout lam K (up S) (allLo S))
        (embP : PlainPart (up S) (allLo S) → PlainPart (shapeOf (Lf ()) t) (annOf (Lf ()) t)) (i : ℕ)
        (ph : Phase lam) (rts : List (Dig lam)) (pls : Plains (up S))
        (z : Rho (up S) × RootsOfChain lam (up S) × Phase lam),
      ph.slotVal = none →
      chainP Lf g early late t cms x salt rtreq S (allLo S) W embP i ph rts pls = some z →
      z.2.2.slotVal = none
  | [], _, _, _, ph, _, _, z, hp, h => by
    have e : z = ((), (), ph) := (Option.some.inj h).symm
    rw [e]
    exact hp
  | r :: S, (w, W), embP, i, ph, rts, (pl, pls), z, hp, h => by
    cases ph with
    | first =>
      simp only [chainP, actOf] at h
      split at h
      · obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 h
        exact chainP_local early late t cms x salt rtreq S W _ (i + 1) _ _ pls y rfl hy
      · cases h
    | loc ρ =>
      simp only [chainP, actOf] at h
      split at h
      · obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 h
        exact chainP_local early late t cms x salt rtreq S W _ (i + 1) _ _ pls y rfl hy
      · cases h
    | shr _ _ => cases hp
    | aft _ _ => cases hp

/-! ### What the forests' leaf queries are -/

/-- A check's leaf query: a symbol's body under emb, and a salt of sMT bits. -/
def InpOK {Pos : Type} {Sym : Pos → Type} (sMT : ℕ)
    (emb : (p : Pos) → Sym p → Body (Lf ())) (c : Check lam (Lf ())) : Prop :=
  ∃ p a salt, c.inp = ⟨emb p a, salt⟩ ∧ salt.length = sMT

theorem compP_inp (sMT : ℕ) (r : RS) (posAt : ℕ → Option r.Pos) (depth : ℕ)
    (emb : (p : r.Pos) → r.Sym p → Body (Lf ())) (rt : Dig lam) (isRead : r.Pos → Bool)
    (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) :
    ∀ (js : List ℕ) (cs : List (Check lam (Lf ()))), compP Lf r posAt depth emb rt isRead f js =
        some cs →
      (∀ j ∈ js, ∀ p, posAt j = some p → ∀ op, f p = some op → op.salt.length = sMT) →
      ∀ c ∈ cs, InpOK Lf sMT emb c
  | [], cs, h, _, c, hc => by
    rw [← Option.some.inj h] at hc
    cases hc
  | j :: js, cs, h, hs, c, hc => by
    have ih := fun cs' h' =>
      compP_inp sMT r posAt depth emb rt isRead f js cs' h'
        (fun i hi => hs i (List.mem_cons_of_mem _ hi))
    simp only [compP] at h
    split at h
    · rename_i p hp
      split at h
      · split at h
        · rename_i op cs' e1 e2
          rw [← Option.some.inj h] at hc
          rcases List.mem_cons.1 hc with rfl | hc
          · exact ⟨p, op.sym, op.salt, rfl, hs j (List.mem_cons_self) p hp op e1⟩
          · exact ih cs' e2 c hc
        · cases h
      · exact ih cs h c hc
    · exact ih cs h c hc

theorem sCompP_len (sMT : ℕ) (r : RS) (posAt : ℕ → Option r.Pos) (depth : ℕ) (hasRoot : Bool)
    (isRead : r.Pos → Bool) (f : (p : r.Pos) → Option (Opening lam (r.Sym p)))
    (h : sCompP sMT r posAt depth hasRoot isRead f = true) :
    ∀ j ∈ List.range (2 ^ depth),
      ∀ p, posAt j = some p → ∀ op, f p = some op → op.salt.length = sMT := by
  intro j hj p hp op hop
  unfold sCompP at h
  rw [List.all_eq_true] at h
  have := h j hj
  rw [hp] at this
  simp only [hop, Bool.and_eq_true, decide_eq_true_eq] at this
  exact this.2

theorem optP_inp (sMT : ℕ) (r : RS) (posAt : ℕ → Option r.Pos) (depth : ℕ)
    (emb : (p : r.Pos) → r.Sym p → Body (Lf ())) (rt : Option (Dig lam)) (isRead : r.Pos → Bool)
    (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) (hasRoot : Bool)
    (hs : sCompP sMT r posAt depth hasRoot isRead f = true) (cs : List (Check lam (Lf ())))
    (h : optP Lf r posAt depth emb rt isRead f = some cs) :
    ∀ c ∈ cs, InpOK Lf sMT emb c := by
  unfold optP at h
  cases rt with
  | none =>
    intro c hc
    rw [← Option.some.inj h] at hc
    cases hc
  | some d =>
    exact compP_inp Lf sMT r posAt depth emb d isRead f _ cs h
      (sCompP_len sMT r posAt depth hasRoot isRead f hs)

theorem mem_flat_split (pr : Bool) (F : Forest lam (Lf ()))
    (c : Check lam (Lf ())) (h : c ∈ flatP Lf (splitP Lf pr F)) : c ∈ F.cs.map Prod.snd := by
  unfold flatP splitP at h
  cases pr with
  | true => simpa using h
  | false =>
    simp only [Bool.false_eq_true, if_false, List.mem_flatMap, List.mem_map] at h
    obtain ⟨F', ⟨e, he, rfl⟩, e', he', rfl⟩ := h
    rw [List.mem_singleton] at he'
    subst he'
    exact List.mem_map_of_mem he

theorem flatP_append (Fs Gs : List (Forest lam (Lf ()))) :
    flatP Lf (Fs ++ Gs) = flatP Lf Fs ++ flatP Lf Gs :=
  List.flatMap_append

/-- The leaf queries of the forests over the prover's messages, where the strict format of the
openings holds: a symbol's body, and a salt of the format's length. -/
theorem forestsP_inp (sMT : ℕ) :
    ∀ (S : List RS) (A : RoundSplits (up S)) (W : RoundsQueryLayout lam K (up S) A)
        (emb : (p : OPos (up S)) → OSym (up S) p → Body (Lf ())) (rts : RootsOfChain lam (up S))
        (isRead : OPos (up S) → Bool) (f : (p : OPos (up S)) → Option (Opening lam (OSym (up S) p)))
        (Fs : List (Forest lam (Lf ()))),
      forestsP Lf S A W emb rts isRead f = some Fs →
      sSP sMT S A W rts isRead f = true → ∀ c ∈ flatP Lf Fs, InpOK Lf sMT emb c
  | [], _, _, _, _, _, _, Fs, h, _, c, hc => by
    rw [← Option.some.inj h] at hc
    cases hc
  | r :: S, (_, A), (w, W), emb, (rt, rts), isRead, f, Fs, h, hs, c, hc => by
    simp only [sSP, Bool.and_eq_true] at hs
    simp only [forestsP] at h
    split at h
    · rename_i a b cc e1 e2 e3
      rw [← Option.some.inj h, flatP_append, flatP_append] at hc
      have lift : ∀ c : Check lam (Lf ()),
          InpOK Lf sMT (Pos := r.Pos) (Sym := r.Sym) (fun p => emb (.inl p)) c →
          InpOK Lf sMT emb c := by
        intro c hc
        obtain ⟨p, a, s, h1, h2⟩ := hc
        exact ⟨.inl p, a, s, h1, h2⟩
      rcases List.mem_append.1 hc with hc | hc
      · have := mem_flat_split Lf _ _ c hc
        simp only [List.map_map, Function.comp_def, List.map_id'] at this
        exact lift c (optP_inp Lf sMT r w.posAt0 w.depth0 _ _ _ _ _ hs.1.1 a e1 c this)
      · rcases List.mem_append.1 hc with hc | hc
        · have := mem_flat_split Lf _ _ c hc
          simp only [List.map_map, Function.comp_def, List.map_id'] at this
          exact lift c (optP_inp Lf sMT r w.posAtJ w.depthJ _ _ _ _ _ hs.1.2 b e2 c this)
        · obtain ⟨p, a', s, h1, h2⟩ := forestsP_inp sMT S A W _ rts _ _ cc e3 hs.2 c hc
          exact ⟨.inr p, a', s, h1, h2⟩
    · cases h

variable {Y : Type} {E : ExtSpec}

/-- All leaf queries of the verifier's forests Fs (`hf`), where the strict format holds (`hs`) and
the wiring lists no external position (`hE`): each is `InpOK`. -/
theorem forestsOfP_inp (sMT sFS : ℕ) (P : PS Y E) (wq : ProtocolQueryLayout lam K P.up)
    (embS : (p : OPos (up P.S)) → OSym (up P.S) p → Body (Lf ())) (embE : E.Sym → Body (Lf ()))
    (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam P.up) (ρ : Rho (up P.S))
    (rts : RootsOfChain lam (up P.S)) (ph : Phase lam)
    (hs : strictP sMT sFS P wq depthReq x π ρ rts ph = true) (hE : wq.ext.all = [])
    (Fs : List (Forest lam (Lf ()))) (hf : forestsOfP Lf P wq embS embE cms x π ρ rts = some Fs) :
    ∀ c ∈ flatP Lf Fs, InpOK Lf sMT embS c := by
  intro c hc
  simp only [strictP, Bool.and_eq_true] at hs
  have h3 := hs.1.1.1.2
  simp only [forestsOfP] at hf
  split at hf
  · rename_i a b e1 e2
    rw [← Option.some.inj hf, flatP_append] at hc
    rcases List.mem_append.1 hc with hc | hc
    · exact forestsP_inp Lf sMT P.S P.ann wq.sh embS rts _ π.opens a e1 h3 c hc
    · exfalso
      unfold forestExtP at e2
      rw [hE] at e2
      have e3 : b = splitP Lf wq.ext.pr ⟨wq.ext.depth, fun t => cms.getD t default, []⟩ :=
        (Option.some.inj e2).symm
      rw [e3] at hc
      have := mem_flat_split Lf _ _ c hc
      cases this
  · cases hf

end

end Run.Thin
