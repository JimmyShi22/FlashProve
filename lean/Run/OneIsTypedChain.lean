-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/OneIsTypedChain.lean: every chain query that the evaluable form of the compiled verifier forms
can be written by the encoding, whatever the oracle functions answer (`askP_all`, under its
hypotheses).

A part of the proof that the run over a single oracle is the run at typed oracle functions
(`one_is_typed`, Run/OneIsTypedTop.lean, under its hypotheses), for the generic construction. The
evaluable form is `verifyP` (Run/ThinDefs.lean; "thin" in names); its chain is `chainP`, and `askP`
(Run/ThinAsked.lean) says that every chain query which `chainP` forms passes a test. Why for every
family of oracle functions: whether a chain query fits (`fitFb`, Run/OneIsTyped.lean) does not
depend on the answers, because a chain value is the list of a digest's 256 bits, whatever the digest
is. So the chain need not be evaluated.

1. What the file contains.
   `nonceOK`, `noncesOK`; `RootsFit ds`.

2. What is checked when the file compiles. Nothing beyond the proofs.

3. Theorems.
   `askP_all`: `OKQ S = true`, K + 1 < 2^48, kinds and work below 256, a salt of 256 bits,
     `S.statement.size < 2^64`, `RootsFit`, fewer than 2^64 rounds and `noncesOK` imply
     `askP .. = true` at every family g.

4. What is not claimed. That these hypotheses hold for a description or for a string:
   Run/OneIsTypedTop.lean. No statement on soundness follows.

Terms: lean/GLOSSARY.md.
-/
import Run.OneIsTyped
import Run.PageIsChain

set_option autoImplicit false

namespace Run.PQ
open Rom Iop Compile Compile.Batch Run.Thin Run.Twin
open _root_.Fmt (Item)

/-- A round's nonce fits its word: it is below 2^64 (nothing is asked of a round without work). -/
def nonceOK {P : Type} : (w : ℕ) → GPlain ℕ w P → Prop
  | 0, _ => True
  | _ + 1, (p : P × ℕ) => p.2 < 2 ^ 64

def noncesOK (C : CK) : (ds : List RD) → Plains (uL C ds) → Prop
  | [], _ => True
  | d :: ds, (pl, pls) => nonceOK d.entry.work pl ∧ noncesOK C ds pls

/-- "Root or none" as the round's tree says fits the round's items. -/
def RootsFit (ds : List RD) : Prop :=
  ∀ d ∈ ds, ∀ rt : Option (Dig 256), rt.isSome = d.tree.isSome → (toRoots d.items rt).isSome = true

theorem takeRt_isSome {lam : ℕ} (has : Bool) (rts rts' : List (Dig lam)) (rt : Option (Dig lam))
    (h : takeRt has rts = some (rt, rts')) : rt.isSome = has := by
  unfold takeRt at h
  cases has with
  | true =>
    cases rts with
    | nil => cases h
    | cons a l =>
      have := Option.some.inj h
      rw [← (Prod.mk.inj this).1]
      rfl
  | false =>
    have := Option.some.inj h
    rw [← (Prod.mk.inj this).1]
    rfl

theorem okRound_of (w : ℕ) (l : List Item) (rt : Option (Dig 256)) (p : GPlain ℕ w (PlainOf l))
    (h1 : (toRoots l rt).isSome = true) (h2 : nonceOK w p) : okRound w l rt p = true := by
  cases w with
  | zero => exact h1
  | succ n =>
    show ((toRoots l rt).isSome && decide ((p : PlainOf l × ℕ).2 < 2 ^ 64)) = true
    rw [h1, Bool.true_and, decide_eq_true_iff]
    exact h2

/-- One step of the test `askP` at a local round after the first. -/
theorem askP_lo {I X : Type} {lam K : ℕ} {y : X} (Lf : Unit → BatchProtocol I X)
    (g : Fam (spec lam K (Lf ()))) (t : Tag) (Pq : FbIn lam (Lf ()) t → Bool) (cms : List (Dig lam))
    (salt : Bits) (r : RS) (Ss : List RS) (A : RoundSplits (up Ss))
    (w : WireRB lam K r.up r.lo) (W : RoundsQueryLayout lam K (up Ss) A)
    (embP : PlainPart (up (r :: Ss)) (r.lo, A) → PlainPart (Compile.Batch.shapeOf (Lf ()) t) (annOf (Lf ()) t))
    (i : ℕ) (v : Bits) (rts : List (Dig lam))
    (pl : r.Plain) (pls : Plains (up Ss)) :
    askP Lf g id none t Pq cms (some y : Option X) salt (r :: Ss) (r.lo, A) (w, W) embP i
      (.loc v) rts (pl, pls) =
      match takeRt w.hasJ rts with
      | some (rt, rts') =>
        Pq ⟨i, .f2 none v, rt, embP (.inl (.inr pl))⟩ &&
          askP Lf g id none t Pq cms (some y : Option X) salt Ss A W
            (fun z => embP (.inr z)) (i + 1)
            (.loc (List.ofFn
                (g (OracleName.fb t)
                  (⟨i, .f2 none v, rt,
                    embP (.inl (.inr pl))⟩ : FbIn lam (Lf ()) t) : (Fin K → Dig lam) × Dig lam).2))
            rts' pls
      | none => true := rfl

section
variable (S : _root_.Fmt.Spec) (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)
  (dec : View → Bool) (h : OKQ S = true)

/-- Under the hypotheses of its statement: the chain queries of the rounds after the first round
fit, at every family. -/
theorem askP_tail (g : Fam (spec 256 (K + 1) (LbS C (rds S) dec))) (cm : Dig 256) (salt : Bits)
    (hK : K + 1 < 2 ^ 48) (hkind : ∀ i, (chainQ S C dec).kind i < 256)
    (hwork : ∀ i, (chainQ S C dec).work i < 256) :
    ∀ (ds : List RD) (n : ℕ) (embP : PlainPart (uL C ds) (allLo (SL C ds)) → PBQ S C dec) (ρ : Bits)
        (rts : List (Dig 256)) (pls : Plains (uL C ds)),
      ρ.length = 256 →
      (∀ z, ∃ pl : PBL C (rds S),
        embP z = .inr pl ∧ ∀ k rt, okL C (rds S) (n + k) rt pl = okL C ds k rt (embPL C ds z)) →
      RootsFit ds → noncesOK C ds pls → n + ds.length < 2 ^ 64 →
      askP (lam := 256) (K := K + 1) (fun _ => LbS C (rds S) dec) g id none .onl (fitFb S C K dec h)
          [cm] (some () : Option Unit) salt (SL C ds) (allLo (SL C ds)) (wiresSL C K chal ds) embP
          (n + 1) (.loc ρ) rts pls = true
  | [], _, _, _, _, _, _, _, _, _, _ => rfl
  | d :: ds, n, embP, ρ, rts, (pl, pls), hρ, hemb, hr, hn, hlen => by
    refine (askP_lo (fun _ => LbS C (rds S) dec) g .onl (fitFb S C K dec h) [cm] salt
      (roundS C d) (SL C ds) (allLo (SL C ds)) (wireS C K chal d) (wiresSL C K chal ds) embP
      (n + 1) ρ rts pl pls).trans ?_
    cases ht : takeRt (wireS C K chal d).hasJ rts with
    | none => rfl
    | some x =>
      obtain ⟨rt, rts'⟩ := x
      obtain ⟨pl', he, hk⟩ := hemb (.inl (.inr pl))
      have hlen' : n + (ds.length + 1) < 2 ^ 64 := hlen
      have hfit : fitFb S C K dec h
            (⟨n + 1, .f2 none ρ, rt, embP (.inl (.inr pl))⟩ : FbIn 256 (LfQ S C dec ()) .onl) =
          true := by
        unfold fitFb
        rw [if_neg (Nat.succ_ne_zero n)]
        unfold fitsQ
        simp only [he]
        have h6 : okL C (rds S) n rt pl' = true := by
          have := hk 0 rt
          rw [Nat.add_zero] at this
          rw [this]
          exact okRound_of d.entry.work d.items rt pl
            (hr d List.mem_cons_self rt (takeRt_isSome _ _ _ _ ht)) hn.1
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨⟨⟨⟨⟨hρ, by omega⟩, hkind _⟩, hwork _⟩, hK⟩, h6⟩
      show (fitFb S C K dec h
            (⟨n + 1, .f2 none ρ, rt, embP (.inl (.inr pl))⟩ : FbIn 256 (LfQ S C dec ()) .onl) &&
          _) = true
      rw [hfit, Bool.true_and]
      refine askP_tail g cm salt hK hkind hwork ds (n + 1) (fun z => embP (.inr z)) _ rts' pls
        List.length_ofFn ?_ (fun d' hd' => hr d' (List.mem_cons_of_mem _ hd')) hn.2 (by omega)
      intro z
      obtain ⟨pl2, he2, hk2⟩ := hemb (.inr z)
      refine ⟨pl2, he2, fun k rt => ?_⟩
      have := hk2 (k + 1) rt
      rw [show n + (k + 1) = n + 1 + k by omega] at this
      exact this

/-- The first chain query fits: `OKQ S = true` (`h`); a salt of 256 bits (`hs`); a statement that
can be spelled (`hst`). -/
theorem first_fits (cm : Dig 256) (salt : Bits)
    (hs : salt.length = 256) (hst : S.statement.size < 2 ^ 64) :
    fitFb S C K dec h
        (⟨0, .f1 [cm] (some ()) salt, none,
          embPS C (rds S) dec (.inl (.inr ()))⟩ : FbIn 256 (LfQ S C dec ()) .onl) = true := by
  unfold fitFb
  rw [if_pos rfl]
  show ((pFirst0 S.label (stmQ S) (unstmQ S) (unstm_stmQ S) (stm_unstmQ S)).put
      (cm, some (), salt)).isSome = true
  rw [pFirst0_put S.label (stmQ S) (unstmQ S) (unstm_stmQ S) (stm_unstmQ S) cm (some ())
      salt S.statement rfl hst (Or.inr hs)]
  rfl

/-- Under `h` (`OKQ S = true`), `hK`, `hkind`, `hwork`, `hs`, `hst`, `hr`, `hlen` and `hn`: every
chain query that the verifier forms fits, at every family. -/
theorem askP_all (g : Fam (spec 256 (K + 1) (LbS C (rds S) dec))) (cm : Dig 256) (salt : Bits)
    (hK : K + 1 < 2 ^ 48) (hkind : ∀ i, (chainQ S C dec).kind i < 256)
    (hwork : ∀ i, (chainQ S C dec).work i < 256) (hs : salt.length = 256)
    (hst : S.statement.size < 2 ^ 64) (hr : RootsFit (rds S)) (hlen : (rds S).length < 2 ^ 64)
    (rts : List (Dig 256)) (pls : Plains (uL C (rds S))) (hn : noncesOK C (rds S) pls) :
    askP (lam := 256) (K := K + 1) (fun _ => LbS C (rds S) dec) g id none .onl (fitFb S C K dec h)
        [cm] (some () : Option Unit) salt (PSof C (rds S) dec).S (PSof C (rds S) dec).ann
        (wqS C K chal (rds S) dec).sh (embPS C (rds S) dec) 0 .first rts ((), pls) = true := by
  show (fitFb S C K dec h
        (⟨0, .f1 [cm] (some ()) salt, none,
          embPS C (rds S) dec (.inl (.inr ()))⟩ : FbIn 256 (LfQ S C dec ()) .onl) && _) = true
  rw [first_fits S C K dec h cm salt hs hst, Bool.true_and]
  refine askP_tail S C K chal dec h g cm salt hK hkind hwork (rds S) 0
    (fun z => embPS C (rds S) dec (.inr z)) _ rts pls List.length_ofFn ?_ hr hn (by omega)
  intro z
  exact ⟨embPL C (rds S) z, rfl, fun k rt => by rw [Nat.zero_add]⟩

end

end Run.PQ
