-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K4/BlockLaws.lean: what K4's block (Johnson/Desc/First/K4/Block.lean, fifth form)
says in terms of K4's plain functions: small theorems, for all states, rounds and parameters. They
are the glue between a law on the plain functions (`hearFl`; `formsFront`, `formsFrontNoRows`,
`formsBack`) and a statement about the block's own fields `decide` and `claims`.

1. `hearAt_ok`, `block_decide`, `decide_ok`: where `decide` returns a state, its six tests hold:
nothing is owed in front; the view's rounds fit K4's table; every round is plain; what the lookup
returned is there; HEAR returns; the stretch is used up. And the state returned is the state in
front with the ledger and what was heard laid, and nothing owed: NOTHING ELSE OF THE SEAT IS
WRITTEN.
2. `runOf_ok`, `block_front`, `block_back`, `front_ok`, `back_ok`: a run of claims returns (claims,
state) JUST WHERE what was heard is there and the plain function returns at it and at the ledger;
the claims are its forms in their order, and the state is the state in front with the ledger laid.
3. `Rd.fits_iff`, `fitsAll_length`, `fitsAll_at`, `fitsAll_rows`: where the table fits, there are as
many entries and rounds as rows, and at each place the entry's name, its number of draws, of draws
that are never 0 and of rows are the row's, and the round shows as many items and drawn elements as
the row says.

No axiom beyond Lean's own. NO SOUNDNESS IS CLAIMED: these say what the block's fields are.

-/
import Johnson.Desc.First.K4.Block
import OnBytes.Desc.First.FlStepLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4
open OnBytes OnBytes.Model OnBytes.Model.Layer OnBytes.K.Kc
open VerifiableInference.Desc (named)

variable {S : Type} (L : Seat S)

/-! ## 1 decide -/

/-- Where HEAR at a place returns a state: its six tests, and the frame. -/
theorem hearAt_ok {p : Par} {s s' : S} {rs : List Fmt.RoundView} (h : hearAt L p s rs = .ok s') :
    (L.owed s).isNone = true ∧
    fitsAll (rounds p.P p.hp p.g) (entries p.P p.hp p.g) rs = true ∧
    Kit.plainStretchWith rowsTabled (entries p.P p.hp p.g) rs = true ∧
    ∃ fo o F, L.look s = some fo ∧
      hearFl { p.P with tokv := L.tokv s } p.hp p.g fo (L.fork s)
        (paired rs (entries p.P p.hp p.g)) = some (o, F, []) ∧
      s' = L.setOwed (L.setOwn (L.setFork s F) o) none := by
  unfold hearAt at h
  cases h1 : (L.owed s).isNone with
  | false => simp [test, VerifiableInference.Desc.need, h1, bind, Except.bind] at h
  | true =>
    cases h2 : fitsAll (rounds p.P p.hp p.g) (entries p.P p.hp p.g) rs with
    | false => simp [test, VerifiableInference.Desc.need, h1, h2, bind, Except.bind] at h
    | true =>
      cases h3 : Kit.plainStretchWith rowsTabled (entries p.P p.hp p.g) rs with
      | false => simp [test, VerifiableInference.Desc.need, h1, h2, h3, bind, Except.bind] at h
      | true =>
        cases h4 : L.look s with
        | none =>
          simp [test, VerifiableInference.Desc.need, named, h1, h2, h3, h4, bind, Except.bind] at h
        | some fo =>
          cases h5 : hearFl { p.P with tokv := L.tokv s } p.hp p.g fo (L.fork s)
              (paired rs (entries p.P p.hp p.g)) with
          | none =>
            simp [test, VerifiableInference.Desc.need, named, h1, h2, h3, h4, h5, bind,
              Except.bind, throw, throwThe, MonadExceptOf.throw] at h
          | some x =>
            obtain ⟨o, F, t⟩ := x
            cases t with
            | cons a t =>
              simp [test, VerifiableInference.Desc.need, named, h1, h2, h3, h4, h5, bind,
                Except.bind, throw, throwThe, MonadExceptOf.throw] at h
            | nil =>
              simp [test, VerifiableInference.Desc.need, named, h1, h2, h3, h4, h5, bind,
                Except.bind, pure, Except.pure] at h
              exact ⟨rfl, rfl, rfl, fo, o, F, rfl, h5, h.symm⟩

/-- The block's `decide` is HEAR at the place; it looks at no column. -/
theorem block_decide (p : Par) (s : S) (rs : List Fmt.RoundView)
    (cols : List (List (Nat × List UInt64))) : (block L p).decide s rs cols = hearAt L p s rs := rfl

/-- **Where the block's `decide` returns a state.** -/
theorem decide_ok {p : Par} {s s' : S} {rs : List Fmt.RoundView} {cols : List (List (Nat × List UInt64))}
    (h : (block L p).decide s rs cols = .ok s') :
    (L.owed s).isNone = true ∧
    fitsAll (rounds p.P p.hp p.g) (entries p.P p.hp p.g) rs = true ∧
    Kit.plainStretchWith rowsTabled (entries p.P p.hp p.g) rs = true ∧
    ∃ fo o F, L.look s = some fo ∧
      hearFl { p.P with tokv := L.tokv s } p.hp p.g fo (L.fork s)
        (paired rs (entries p.P p.hp p.g)) = some (o, F, []) ∧
      s' = L.setOwed (L.setOwn (L.setFork s F) o) none :=
  hearAt_ok L h

/-! ## 2 claims -/

/-- A run of claims returns just where what was heard is there and the plain function returns. -/
theorem runOf_ok (name : String) (f : Own → Fork → Option (Array Aff × Fork)) (s s' : S)
    (cl : List Aff) :
    runOf L name f s = .ok (cl, s') ↔
      ∃ o fs F, L.own s = some o ∧ f o (L.fork s) = some (fs, F) ∧ cl = fs.toList ∧
        s' = L.setFork s F := by
  unfold runOf
  cases h1 : L.own s with
  | none => simp [named, bind, Except.bind]
  | some o =>
    cases h2 : f o (L.fork s) with
    | none => simp [named, h2, bind, Except.bind]
    | some x =>
      obtain ⟨fs, F⟩ := x
      simp only [named, h2, bind, Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq,
        Option.some.injEq]
      constructor
      · intro h
        exact ⟨o, fs, F, rfl, h2, h.1.symm, h.2.symm⟩
      · intro h
        obtain ⟨o', fs', F', ho, hf, hc, hs⟩ := h
        subst ho
        rw [h2] at hf
        simp only [Option.some.injEq, Prod.mk.injEq] at hf
        obtain ⟨hf1, hf2⟩ := hf
        subst hf1
        subst hf2
        exact ⟨hc.symm, hs.symm⟩

/-- The plain function of the run "front": by who states the lookup's own claims. -/
def frontOf (p : Par) : Own → Fork → Option (Array Aff × Fork) :=
  (if p.k3Runs then formsFrontNoRows else formsFront) p.P p.g

/-- The block's run "front". -/
theorem block_front (p : Par) : (block L p).claims.lookup "front" =
    some fun _ s => runOf L "K4.claims-front" (frontOf p) s := by
  simp [block, frontOf]

/-- The block's run "back". -/
theorem block_back (p : Par) : (block L p).claims.lookup "back" =
    some fun _ s => runOf L "K4.claims-back" formsBack s := by
  simp [block, List.lookup]

/-- **Where the run "front" returns.** n: the number of claims gathered so far: not read. -/
theorem front_ok (p : Par) (run : Nat → S → Except String (List Aff × S))
    (hr : (block L p).claims.lookup "front" = some run) (n : Nat) (s s' : S) (cl : List Aff) :
    run n s = .ok (cl, s') ↔
      ∃ o fs F, L.own s = some o ∧ frontOf p o (L.fork s) = some (fs, F) ∧ cl = fs.toList ∧
        s' = L.setFork s F := by
  rw [block_front] at hr
  simp only [Option.some.injEq] at hr
  subst hr
  exact runOf_ok L _ _ s s' cl

/-- **Where the run "back" returns.** -/
theorem back_ok (p : Par) (run : Nat → S → Except String (List Aff × S))
    (hr : (block L p).claims.lookup "back" = some run) (n : Nat) (s s' : S) (cl : List Aff) :
    run n s = .ok (cl, s') ↔
      ∃ o fs F, L.own s = some o ∧ formsBack o (L.fork s) = some (fs, F) ∧ cl = fs.toList ∧
        s' = L.setFork s F := by
  rw [block_back] at hr
  simp only [Option.some.injEq] at hr
  subst hr
  exact runOf_ok L _ _ s s' cl

/-! ## 3 the table of rounds -/

/-- What it says that a row fits an entry and a round. -/
theorem Rd.fits_iff (d : Rd) (e : Fmt.Entry) (r : Fmt.RoundView) :
    d.fits e r = true ↔
      e.name = d.name.name ∧ r.vals.length = d.sent ∧ e.drawE = d.drawn ∧
        r.drawn.elems.length = d.drawn ∧ e.drawNZ = d.notZero ∧ e.rows = d.rows := by
  unfold Rd.fits
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc]

/-- Where the table fits there are as many entries and as many rounds as rows. -/
theorem fitsAll_length : ∀ (ds : List Rd) (es : List Fmt.Entry) (rs : List Fmt.RoundView),
    fitsAll ds es rs = true → es.length = ds.length ∧ rs.length = ds.length
  | [], [], [], _ => ⟨rfl, rfl⟩
  | [], [], _ :: _, h => absurd (show false = true from h) Bool.false_ne_true
  | [], _ :: _, _, h => absurd (show false = true from h) Bool.false_ne_true
  | _ :: _, [], _, h => absurd (show false = true from h) Bool.false_ne_true
  | _ :: _, _ :: _, [], h => absurd (show false = true from h) Bool.false_ne_true
  | d :: ds, e :: es, r :: rs, h => by
    have h' : (d.fits e r && fitsAll ds es rs) = true := h
    rw [Bool.and_eq_true] at h'
    obtain ⟨a, b⟩ := fitsAll_length ds es rs h'.2
    exact ⟨by simp only [List.length_cons, a], by simp only [List.length_cons, b]⟩

/-- Where the table fits, each row fits its entry and its round. -/
theorem fitsAll_at : ∀ (ds : List Rd) (es : List Fmt.Entry) (rs : List Fmt.RoundView),
    fitsAll ds es rs = true → ∀ (i : Nat) (d : Rd) (e : Fmt.Entry) (r : Fmt.RoundView),
      ds[i]? = some d → es[i]? = some e → rs[i]? = some r → d.fits e r = true
  | [], _, _, _ => fun i d e r hd _ _ => by simp at hd
  | _ :: _, [], _, h => absurd (show false = true from h) Bool.false_ne_true
  | _ :: _, _ :: _, [], h => absurd (show false = true from h) Bool.false_ne_true
  | d0 :: ds, e0 :: es, r0 :: rs, h => by
    have h' : (d0.fits e0 r0 && fitsAll ds es rs) = true := h
    rw [Bool.and_eq_true] at h'
    intro i d e r hd he hr
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hd he hr
      subst hd
      subst he
      subst hr
      exact h'.1
    | succ i =>
      simp only [List.getElem?_cons_succ] at hd he hr
      exact fitsAll_at ds es rs h'.2 i d e r hd he hr

/-- **Where K4's table fits a stretch**: the lengths; and, place by place, the entry's four numbers
and its name are the row's, and the round shows as many items and drawn elements as the row says. -/
theorem fitsAll_rows {ds : List Rd} {es : List Fmt.Entry} {rs : List Fmt.RoundView}
    (h : fitsAll ds es rs = true) :
    es.length = ds.length ∧ rs.length = ds.length ∧
      ∀ (i : Nat) (d : Rd) (e : Fmt.Entry) (r : Fmt.RoundView),
        ds[i]? = some d → es[i]? = some e → rs[i]? = some r →
          e.name = d.name.name ∧ r.vals.length = d.sent ∧ e.drawE = d.drawn ∧
            r.drawn.elems.length = d.drawn ∧ e.drawNZ = d.notZero ∧ e.rows = d.rows :=
  ⟨(fitsAll_length ds es rs h).1, (fitsAll_length ds es rs h).2, fun i d e r hd he hr =>
    (Rd.fits_iff d e r).mp (fitsAll_at ds es rs h i d e r hd he hr)⟩

end OnBytes.Desc.First.K4
