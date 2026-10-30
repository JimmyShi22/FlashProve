-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/AlikeKeep.lean: the masked sumcheck's part with a kept state
(`keepPart`, Honest/SumKeep.lean) and `sumPart` at the earlier job, each placed in a wider state of
its own by `Part.lift`: their rounds are related by `AlikeTo` (Honest/Alike.lean). So this folder's
two players return the same of both. Lemmas with their proofs.

The two wider states. `X`: the state of the prover whose part keeps nothing; `get₁ : X → Y` and
`set₁` place `sumPart` in it. `X'`: the state of the prover whose part keeps something;
`get₂ : X' → Y × Option K` and `set₂` place `keepPart` in it. `r : X → X' → Prop` relates the two.

What is asked of `r`, `get` and `set`.
  * `hgs`: `get₂ (set₂ x' y) = y`.
  * `hg`: related values give the earlier job the same: `r x x' → get₁ x = (get₂ x').1`.
  * `hr`: the two parts' writing keeps the values related:
    `r x x' → r (set₁ x (get₁ x)) (set₂ x' ((get₂ x').1, k))`, at every `k`.
So `r` may say anything that these two writings leave alone: for example what other parts of the
same chain have kept in other fields.

  1  `rest_movesTo`   the moves from a round number on, under the invariant `Kept`
  2  `keep_movesTo`   all moves, whatever kept state there is before the part
  3  `keepPart_reMove`, `alike_lift_keep`, `faced_lift_keep`   the two placed parts' rounds

Limits.
  * `KeepJob.FaithfulOn Ok`, and `Ok` at the state before the part, are hypotheses. At what the
    first is asked: the Limits of Honest/SumKeepLaw.lean.
  * One part. A list of parts, a prover's side or a chain is joined by `AlikeTo.append`.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.AlikeParts
import Johnson.Desc.ProofFile.Honest.SumKeepLift

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.Keep
open OnBytes (E)
open VerifiableInference.Desc (Oracle)
open ProofFile.Honest.SumLaw

variable {V V' W W' X X' Y K : Type}

/-! ## 1 From a round number on -/

/-- The moves from the round number `n` on. `H`: the challenges before the part. `own`, `shown`: the
part's own challenges and rounds so far. `y`: what the earlier job is given. The premise on the two
lists is asked at every value `o` of the columns opened, as in `MovesTo` (Honest/AlikeParts.lean).
-/
theorem rest_movesTo (wit : W → W') (get₁ : X → Y) (set₁ : X → Y → X) (get₂ : X' → Y × Option K)
    (set₂ : X' → Y × Option K → X') (r : X → X' → Prop) (hgs : ∀ x' y, get₂ (set₂ x' y) = y)
    (hg : ∀ x x', r x x' → get₁ x = (get₂ x').1)
    (hr : ∀ x x' k, r x x' → r (set₁ x (get₁ x)) (set₂ x' ((get₂ x').1, k)))
    (J : KeepJob W' Y K) {name endName : String} (c : SumCoins name endName J.base) (i : W)
    (H : List Fmt.Drawn) (y : Y) (S : List Fmt.RoundView) :
    ∀ (l₁ : List (SumCoins name endName J.job → Seen → State W' (Y × Option K) → List E))
      (l₂ : List (SumCoins name endName J.base → Seen → State W' Y → List E)) (n : Nat)
      (own : List Fmt.Drawn) (shown : List Fmt.RoundView) (x : X) (x' : X') (k : Option K),
      (∀ o, Agree J c (wit i) H y ⟨S, o⟩ n l₁ l₂) → own.length = n → shown.length = n → r x x' →
      get₂ x' = (y, k) → Kept J (wit i) H y own k →
      MovesTo (C := SumCoins name endName J.base) c (StateBy r)
        ((l₂.map mvOf).map (Move.lift wit get₁ set₁))
        ((withPass J.pass n (l₁.map mvOf)).map (Move.lift wit get₂ set₂))
        ⟨i, H ++ own, x⟩ ⟨i, H ++ own, x'⟩ (S ++ shown)
  | [], [], _, _, _, _, _, _, _, _, _, hx, _, _ => ⟨rfl, rfl, hx⟩
  | a :: l₁, b :: l₂, n, own, shown, x, x', k, hA, ho, hs, hx, hk, hK => by
    have e1 : get₁ x = y := (hg x x' hx).trans (congrArg Prod.fst hk)
    refine ⟨fun o => ?_, fun d e => ?_⟩
    · show (Except.ok (sayE (b c ((⟨S, o⟩ : Seen).plus shown) ⟨wit i, H ++ own, get₁ x⟩)) :
          Except String Sending) =
        Except.ok (sayE (a c ((⟨S, o⟩ : Seen).plus shown) ⟨wit i, H ++ own, get₂ x'⟩))
      rw [e1, hk, (hA o).head own shown k ho hs hK]
    · obtain ⟨k', hp, hK'⟩ := pass_kept J (wit i) H y n own d k ho hK
      show MovesTo (C := SumCoins name endName J.base) c (StateBy r)
        ((l₂.map mvOf).map (Move.lift wit get₁ set₁))
        ((withPass J.pass (n + 1) (l₁.map mvOf)).map (Move.lift wit get₂ set₂))
        ⟨i, (H ++ own) ++ [d], set₁ x (get₁ x)⟩
        ⟨i, (H ++ own) ++ [d], set₂ x' (J.pass n ⟨wit i, (H ++ own) ++ [d], get₂ x'⟩)⟩
        ((S ++ shown) ++ [e])
      rw [hk, hp, List.append_assoc, List.append_assoc]
      have hy : (get₂ x').1 = y := congrArg Prod.fst hk
      have hx' : r (set₁ x (get₁ x)) (set₂ x' (y, k')) := by
        have q := hr x x' k' hx
        rw [hy] at q
        exact q
      exact rest_movesTo wit get₁ set₁ get₂ set₂ r hgs hg hr J c i H y S l₁ l₂ (n + 1) (own ++ [d])
        (shown ++ [e]) _ _ k' (fun o => (hA o).tail)
        (by rw [List.length_append, ho]; rfl) (by rw [List.length_append, hs]; rfl) hx'
        (hgs _ _) hK'
  | [], _ :: _, _, _, _, _, _, _, hA, _, _, _, _, _ => False.elim (hA none)
  | _ :: _, [], _, _, _, _, _, _, hA, _, _, _, _, _ => False.elim (hA none)

/-! ## 2 All moves -/

/-- **The two placed lists of moves say the same**, whatever kept state there is before the part.
-/
theorem keep_movesTo (wit : W → W') (get₁ : X → Y) (set₁ : X → Y → X) (get₂ : X' → Y × Option K)
    (set₂ : X' → Y × Option K → X') (r : X → X' → Prop) (hgs : ∀ x' y, get₂ (set₂ x' y) = y)
    (hg : ∀ x x', r x x' → get₁ x = (get₂ x').1)
    (hr : ∀ x x' k, r x x' → r (set₁ x (get₁ x)) (set₂ x' ((get₂ x').1, k)))
    (J : KeepJob W' Y K) {name endName : String} (c : SumCoins name endName J.base)
    (Ok : W' → List Fmt.Drawn → Y → Prop) (hJ : J.FaithfulOn Ok) (t : State W X)
    (t' : State W X') (seen : List Fmt.RoundView) (ht : StateBy r t t')
    (hOk : Ok (wit t.input) t.heard (get₁ t.own)) :
    MovesTo (C := SumCoins name endName J.base) c (StateBy r)
      ((sumPart (V := V') name endName J.base).moves.map (Move.lift wit get₁ set₁))
      ((keepPart (V := V') name endName J).moves.map (Move.lift wit get₂ set₂)) t t' seen := by
  obtain ⟨i, H, x⟩ := t
  obtain ⟨i', H', x'⟩ := t'
  obtain ⟨q1, q2, q3⟩ := ht
  have e1 : i = i' := q1
  have e2 : H = H' := q2
  have hx : r x x' := q3
  subst e1 e2
  have hOk' : Ok (wit i) H (get₁ x) := hOk
  have hA : ∀ o, Agree J c (wit i) H (get₁ x) ⟨seen, o⟩ 0
      (askG name endName J.job (saidFirst J.job) 0 :: restGs name endName J.job)
      (askG name endName J.base (saidFirst J.base) 0 :: restGs name endName J.base) :=
    fun o => agree_all J hJ c (wit i) H (get₁ x) hOk' ⟨seen, o⟩
  have eK : (keepPart (V := V') name endName J).moves = withPass J.pass 0
      ((askG name endName J.job (saidFirst J.job) 0 :: restGs name endName J.job).map mvOf) :=
    keepPart_moves name endName J
  have eS : (sumPart (V := V') name endName J.base).moves =
      (askG name endName J.base (saidFirst J.base) 0 :: restGs name endName J.base).map mvOf :=
    sumPart_moves name endName J.base
  rw [eK, eS]
  have ey : get₁ x = (get₂ x').1 := hg x x' hx
  refine ⟨fun o => ?_, fun d e => ?_⟩
  · show (Except.ok (sayE (askG name endName J.base (saidFirst J.base) 0 c ⟨seen, o⟩
        ⟨wit i, H, get₁ x⟩)) : Except String Sending) =
      Except.ok (sayE (askG name endName J.job (saidFirst J.job) 0 c ⟨seen, o⟩
        ⟨wit i, H, get₂ x'⟩))
    rw [ey]
    rfl
  · obtain ⟨k', hp, hK'⟩ := pass_kept J (wit i) H (get₁ x) 0 [] d none rfl (Or.inl rfl)
    have hp' : J.pass 0 ⟨wit i, H ++ [d], get₂ x'⟩ = (get₁ x, k') := by
      have e0 : get₂ x' = (get₁ x, (get₂ x').2) := by rw [ey]
      rw [e0, pass_zero]
      rw [List.append_nil] at hp
      exact hp
    show MovesTo (C := SumCoins name endName J.base) c (StateBy r)
      (((restGs name endName J.base).map mvOf).map (Move.lift wit get₁ set₁))
      ((withPass J.pass (0 + 1) ((restGs name endName J.job).map mvOf)).map
        (Move.lift wit get₂ set₂))
      ⟨i, H ++ [d], set₁ x (get₁ x)⟩ ⟨i, H ++ [d], set₂ x' (J.pass 0 ⟨wit i, H ++ [d], get₂ x'⟩)⟩
      (seen ++ [e])
    rw [hp']
    have hx' : r (set₁ x (get₁ x)) (set₂ x' (get₁ x, k')) := by
      have q := hr x x' k' hx
      rw [← ey] at q
      exact q
    exact rest_movesTo wit get₁ set₁ get₂ set₂ r hgs hg hr J c i H (get₁ x) seen
      (restGs name endName J.job) (restGs name endName J.base) 1 [d] [e] _ _ k'
      (fun o => (hA o).tail) rfl rfl hx'
      (hgs _ _) hK'

/-! ## 3 The two placed parts' rounds -/

/-- `keepPart` is `sumPart` at the earlier job with other moves. -/
theorem keepPart_reMove (name endName : String) (J : KeepJob W Y K) :
    keepPart (V := V) name endName J =
      (sumPart (V := V) name endName J.base).reMove (keepPart (V := V) name endName J).moves :=
  rfl

/-- **The rounds of the two placed parts are related.** -/
theorem alike_lift_keep (see : V → V') (wit : W → W') (get₁ : X → Y) (set₁ : X → Y → X)
    (get₂ : X' → Y × Option K) (set₂ : X' → Y × Option K → X') (r : X → X' → Prop)
    (hgs : ∀ x' y, get₂ (set₂ x' y) = y) (hg : ∀ x x', r x x' → get₁ x = (get₂ x').1)
    (hr : ∀ x x' k, r x x' → r (set₁ x (get₁ x)) (set₂ x' ((get₂ x').1, k)))
    (name endName : String) (J : KeepJob W' Y K) (Ok : W' → List Fmt.Drawn → Y → Prop)
    (hJ : J.FaithfulOn Ok) (c : SumCoins name endName J.base) (nm : String) (a : Addr)
    (rs : List (Fmt.DeclaredRound × List Oracle)) (v : Option V) (m : Mid W X) (m' : Mid W X')
    (hrs : rs.length = (scalarsOf J.base.shape).length) (hm : MidBy (StateBy r) m m')
    (hOk : Ok (wit m.st.input) m.st.heard (get₁ m.st.own)) :
    AlikeTo (MidBy (StateBy r))
      (((sumPart (V := V') name endName J.base).lift see wit get₁ set₁).steps nm a rs v c)
      (((keepPart (V := V') name endName J).lift see wit get₂ set₂).steps nm a rs v c) m m' := by
  have hn₁ : ((sumPart (V := V') name endName J.base).moves.map
      (Move.lift wit get₁ set₁)).length = (scalarsOf J.base.shape).length := by
    rw [List.length_map]
    exact sumPart_rounds name endName J.base
  have hn₂ : ((keepPart (V := V') name endName J).moves.map
      (Move.lift wit get₂ set₂)).length = (scalarsOf J.base.shape).length := by
    rw [List.length_map]
    exact keepPart_rounds name endName J
  exact steps_alike ((sumPart (V := V') name endName J.base).lift see wit get₁ set₁)
    ((keepPart (V := V') name endName J).moves.map (Move.lift wit get₂ set₂)) nm a rs v c
    (StateBy r) m m' (hn₂.trans hn₁.symm) (hrs.trans hn₁.symm) hm.1 hm.2.1
    (keep_movesTo wit get₁ set₁ get₂ set₂ r hgs hg hr J c Ok hJ m.st m'.st m.seen hm.2.2 hOk)

/-- What a player reads of the two parts' rounds beside their moves is the same. -/
theorem faced_lift_keep (see : V → V') (wit : W → W') (get₁ : X → Y) (set₁ : X → Y → X)
    (get₂ : X' → Y × Option K) (set₂ : X' → Y × Option K → X') (name endName : String)
    (J : KeepJob W' Y K) (c : SumCoins name endName J.base) (nm : String) (a : Addr)
    (rs : List (Fmt.DeclaredRound × List Oracle)) (v : Option V) :
    FacedAll
      (((sumPart (V := V') name endName J.base).lift see wit get₁ set₁).steps nm a rs v c)
      (((keepPart (V := V') name endName J).lift see wit get₂ set₂).steps nm a rs v c) := by
  have hn₁ : ((sumPart (V := V') name endName J.base).moves.map
      (Move.lift wit get₁ set₁)).length = (scalarsOf J.base.shape).length := by
    rw [List.length_map]
    exact sumPart_rounds name endName J.base
  have hn₂ : ((keepPart (V := V') name endName J).moves.map
      (Move.lift wit get₂ set₂)).length = (scalarsOf J.base.shape).length := by
    rw [List.length_map]
    exact keepPart_rounds name endName J
  exact steps_faced ((sumPart (V := V') name endName J.base).lift see wit get₁ set₁)
    ((keepPart (V := V') name endName J).moves.map (Move.lift wit get₂ set₂)) nm a rs v c
    (hn₂.trans hn₁.symm)

end ProofFile.Honest.Keep

#print axioms ProofFile.Honest.Keep.rest_movesTo
#print axioms ProofFile.Honest.Keep.keep_movesTo
#print axioms ProofFile.Honest.Keep.keepPart_reMove
#print axioms ProofFile.Honest.Keep.alike_lift_keep
#print axioms ProofFile.Honest.Keep.faced_lift_keep
