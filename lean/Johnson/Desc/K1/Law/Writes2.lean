-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/Writes2.lean: what the loop over a sending's messages asks and writes.

Main names: put, admD; wr_eq, admD_toList; layRows_iff: the loop says yes just where the counts fit,
and then the statement's messages are those in front with the new ones as outs writes them.
Plain records and pure functions of the verifier program are named, none that takes a context or
runs: Send.pad, Slice.admitted, Slice.freshLedger.

What is not claimed. Nothing on what a row means, on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.K1.Law.Writes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain

variable {L : Type}

/-- The record with other oracle messages in its statement. -/
def put (d : DState L) (l : List OnBytes.Oracle) : DState L :=
  { d with st := { d.st with oracles := l.toArray } }

theorem put_self (d : DState L) (l : List OnBytes.Oracle) (h : d.st.oracles.toList = l) :
    put d l = d := by
  subst h
  simp [put]

theorem wr_eq (codes : Codes) (seeds : List (List E × E)) (o : Nat) (s : OracleShape) (ys : List E)
    (places : List PadPlace) (h0 : s.answers ≠ 0) (hp : Send.pad codes s = some places) :
    wr codes seeds o s ys =
      { fresh s with
        sampled := true, sampleRows := rowsOf codes seeds o s ys
        pad := places.map fun p => (p.part, p.index), ledger := Slice.freshLedger codes s } := by
  simp [wr, h0, hp, fresh]

/-- The record behind one admitted sample. -/
@[reducible] def admD (d : DState L) (o : Nat) (s : OracleShape) (places : List PadPlace)
    (rows : Array OnBytes.Row) : DState L :=
  { d with st := Slice.admitted d.st o s places rows }

theorem admD_toList (codes : Codes) (seeds : List (List E × E)) (d : DState L)
    (pre : List OnBytes.Oracle) (l : List OracleShape) (s : OracleShape) (ys : List E)
    (places : List PadPlace) (hc : d.st.codes = codes)
    (hA : d.st.oracles.toList = pre ++ fresh s :: l.map fresh) (h0 : s.answers ≠ 0)
    (hp : Send.pad codes s = some places) :
    (admD d pre.length s places (rowsOf codes seeds pre.length s ys)).st.oracles.toList =
      (pre ++ [wr codes seeds pre.length s ys]) ++ l.map fresh := by
  have := toList_modify_mid d.st.oracles pre (l.map fresh) (fresh s) (fun x => { x with
    sampled := true, sampleRows := rowsOf codes seeds pre.length s ys
    pad := places.map fun p => (p.part, p.index), ledger := Slice.freshLedger d.st.codes s }) hA
  show (d.st.oracles.modify pre.length _).toList = _
  rw [this, wr_eq codes seeds pre.length s ys places h0 hp, hc]
  simp

theorem layRows_iff (codes : Codes) (seeds : List (List E × E)) :
    ∀ (shapes : List OracleShape) (pre : List OnBytes.Oracle) (ys : List E) (d d' : DState L),
      d.st.codes = codes → d.st.oracles.toList = pre ++ shapes.map fresh →
      (layRows codes seeds (tag pre.length shapes) ys d = .ok d' ↔
        fitB codes seeds.length shapes ys = true ∧
          d' = put d (pre ++ outs codes seeds pre.length shapes ys))
  | [], pre, ys, d, d', _, hA => by
    have hd : put d (pre ++ outs codes seeds pre.length [] ys) = d :=
      put_self d _ (by simpa [outs] using hA)
    rw [hd]
    cases ys <;> simp [tag, layRows, fitB, eq_comm]
  | s :: l, pre, ys, d, d', hc, hA => by
    have hA' : d.st.oracles.toList = pre ++ fresh s :: l.map fresh := by simpa using hA
    have e : tag pre.length (s :: l) = (pre.length, s) :: tag (pre.length + 1) l := rfl
    rw [e]
    by_cases h0 : s.answers = 0
    · have ih := layRows_iff codes seeds l (pre ++ [fresh s]) ys d d' hc (by simp [hA'])
      rw [List.length_append, List.length_singleton] at ih
      have e1 : layRows codes seeds ((pre.length, s) :: tag (pre.length + 1) l) ys d =
          layRows codes seeds (tag (pre.length + 1) l) ys d := by
        rw [layRows]; simp [h0]
      rw [e1, ih]
      simp [fitB, outs, wr, h0]
    · by_cases hs : s.answers ≤ seeds.length
      · by_cases hy : s.answers ≤ ys.length
        · have hx := get_mid _ _ _ _ hA'
          have hr := rowsOf_size codes seeds pre.length s ys hs hy
          have e1 : layRows codes seeds ((pre.length, s) :: tag (pre.length + 1) l) ys d =
              (named "K1: the statement does not admit the sample"
                (Ground.admitP d pre.length (rowsOf codes seeds pre.length s ys))).bind
                (layRows codes seeds (tag (pre.length + 1) l) (ys.drop s.answers)) := by
            rw [layRows]
            simp [h0, Nat.not_lt.2 hs, Nat.not_lt.2 hy, rowsOf]
          rw [e1]
          constructor
          · intro h
            obtain ⟨d₁, h1, h2⟩ := (bind_ok _ _ _).1 h
            obtain ⟨places, hp, rfl⟩ := (admitP_iff d d₁ _ s _ hx hr h0).1 ((named_ok _ _ _).1 h1)
            rw [hc] at hp
            have ih := layRows_iff codes seeds l (pre ++ [wr codes seeds pre.length s ys])
              (ys.drop s.answers) (admD d pre.length s places (rowsOf codes seeds pre.length s ys))
              d' hc (admD_toList codes seeds d pre l s ys places hc hA' h0 hp)
            rw [List.length_append, List.length_singleton] at ih
            obtain ⟨f1, f2⟩ := ih.1 h2
            refine ⟨by simp [fitB, h0, hs, hy, hp, f1], ?_⟩
            rw [f2]
            simp [put, outs, Slice.admitted]
          · rintro ⟨f, rfl⟩
            simp only [fitB, h0, if_false, hs, hy, decide_true, Bool.true_and,
              Bool.and_eq_true] at f
            obtain ⟨places, hp⟩ := Option.isSome_iff_exists.1 f.1
            have ih := layRows_iff codes seeds l (pre ++ [wr codes seeds pre.length s ys])
              (ys.drop s.answers) (admD d pre.length s places (rowsOf codes seeds pre.length s ys))
              (put d (pre ++ outs codes seeds pre.length (s :: l) ys)) hc
              (admD_toList codes seeds d pre l s ys places hc hA' h0 hp)
            rw [List.length_append, List.length_singleton] at ih
            refine (bind_ok _ _ _).2 ⟨_, (named_ok _ _ _).2
              ((admitP_iff d _ _ s _ hx hr h0).2 ⟨places, by rw [hc]; exact hp, rfl⟩), ?_⟩
            refine ih.2 ⟨f.2, ?_⟩
            simp [put, outs, Slice.admitted]
        · have e1 : layRows codes seeds ((pre.length, s) :: tag (pre.length + 1) l) ys d =
              .error "K1: an answer lacks for a row" := by
            rw [layRows]; simp [h0, Nat.not_lt.2 hs, Nat.lt_of_not_le hy]
          rw [e1]
          simp [fitB, h0, hy]
      · have e1 : layRows codes seeds ((pre.length, s) :: tag (pre.length + 1) l) ys d =
            .error "K1: a seed lacks for an answer" := by
          rw [layRows]; simp [h0, Nat.lt_of_not_le hs]
        rw [e1]
        simp [fitB, h0, hs]

end VerifiableInference.Desc.K1
