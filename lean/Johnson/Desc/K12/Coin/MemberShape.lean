-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Coin/MemberShape.lean: **A MEMBER's SHAPE AND SAMPLE ROWS, IN THE PLAIN DATA THAT A
STATE FIXES, ARE THOSE OF THE STATE's OWN MESSAGE.** Statements and proofs. For the seam from the
proximity test's conclusion to the table's: so that a fact on the message of the STATE IN FRONT
("its shape is the plan's", "it is sampled", "its one sample row is …") reaches the clauses that are
asked at the plain data's members.
What a state t in front fixes (`Fixes`, Sheet.lean): the first stage a, the group G0, its layout
Ly, and the plain data D made at the state behind the batching's beginning (`gpOf` at
`begun t.st t.g G0`). Between t.st and D.st lie: the beginning of the test (it shuts ledgers) and,
in the own mask's arm, the receiving of the first fold's mask (it appends one message).
  `begun_get`: the beginning of a test leaves a message's shape, "sampled" and sample rows.
  `member_at`: GENERAL IN THE CHAIN AND THE ARM: at a member j whose number is below the state's
    number of messages: the state's message x and the plain data's x' are there;
    (D.mems.get j).sh = x.shape; x'.shape = x.shape; x'.sampled = x.sampled;
    x'.sampleRows = x.sampleRows.
  `member_below_first`: where the state names a mask (the first arm) every member's number IS
    below.
  `member_shape`, `member_shape_first`: the first clause alone.
THE CORNER. In the own mask's arm "below" is a PREMISE, and it cannot be dropped by type: the
layout takes the group's members as they stand (`Statement.layout` asks of no member that its
message is there): a state whose group names the number that the NEXT message will bear would make
a member of the fresh mask itself, and the state in front has no message of that number.
Limits. Nothing on soundness.

-/
import Johnson.Desc.K12.Coin.Sheet
import Johnson.Desc.K12.Law.TieFront

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.First (Plain Made made_of gpOf entered)

/-- The beginning of a test leaves a message's shape, "sampled" and sample rows. -/
theorem begun_get (S : Statement) (g : ℕ) (G : Group) (o : ℕ) (x' : OnBytes.Oracle)
    (h : (begun S g G).oracles[o]? = some x') :
    ∃ x, S.oracles[o]? = some x ∧ x'.shape = x.shape ∧ x'.sampled = x.sampled ∧
      x'.sampleRows = x.sampleRows := by
  have e : (begun S g G).oracles[o]? = (S.oracles[o]?).map fun x =>
      if o ∈ G.members.toList then shut x else x := closeLedgers_get _ _ _
  rw [e] at h
  obtain ⟨x, hx, h⟩ := Option.map_eq_some_iff.1 h
  refine ⟨x, hx, ?_⟩
  subst h
  split <;> exact ⟨rfl, rfl, rfl⟩

theorem begun_size (S : Statement) (g : ℕ) (G : Group) :
    (begun S g G).oracles.size = S.oracles.size := closeLedgers_size _ _

section
variable {π : P12} {t : T12} {a : Fmt.M1.Stage} {rest : List Fmt.M1.Stage} {G0 : Group}
  {Ly : GroupLayout} {D : Plain}

/-- **At a member whose number is below the state's number of messages.** -/
theorem member_at (hf : Fixes π t a rest G0 Ly D) (j : Fin D.mems.length)
    (hlt : (D.mems.get j).id < t.st.oracles.size) :
    ∃ x x', t.st.oracles[(D.mems.get j).id]? = some x ∧
      D.st.oracles[(D.mems.get j).id]? = some x' ∧ (D.mems.get j).sh = x.shape ∧
      x'.shape = x.shape ∧ x'.sampled = x.sampled ∧ x'.sampleRows = x.sampleRows := by
  have hm := made_of π _ a Ly D (hf.2.2.2 default)
  obtain ⟨x', hx', hs⟩ := (hm.mem j).2.oracle
  have e := H2K.Pin.oracle_made hm (D.mems.get j).id (by
    show _ < (begun t.st t.g G0).oracles.size
    rw [begun_size]
    exact hlt)
  have hx1 : (begun t.st t.g G0).oracles[(D.mems.get j).id]? = some x' := by
    rw [← hx']
    exact e.symm
  obtain ⟨x, hx, s1, s2, s3⟩ := begun_get _ _ _ _ _ hx1
  exact ⟨x, x', hx, hx', by rw [← hs, s1], s1, s2, s3⟩

/-- Where the state names a mask, every member's number is below. -/
theorem member_below_first (hf : Fixes π t a rest G0 Ly D) (hmk : t.mask.isSome = true)
    (j : Fin D.mems.length) : (D.mems.get j).id < t.st.oracles.size := by
  have hm := made_of π _ a Ly D (hf.2.2.2 default)
  obtain ⟨x', hx', _⟩ := (hm.mem j).2.oracle
  obtain ⟨cu, _, he⟩ := hm.ent
  obtain ⟨id, hid⟩ := Option.isSome_iff_exists.1 hmk
  have he' : entered π { t with st := begun t.st t.g G0, pass := .claim default Ly } cu Ly =
      some (id, begun t.st t.g G0, t.book) := by
    unfold entered
    show (match t.mask with
      | some id => some (id, begun t.st t.g G0, t.book)
      | none => _) = _
    rw [hid]
  rw [he'] at he
  have e : begun t.st t.g G0 = D.st := congrArg (fun x => x.2.1) (Option.some.inj he)
  rw [← e] at hx'
  have := (Array.getElem?_eq_some_iff.1 hx').1
  rwa [begun_size] at this

/-- The first clause alone. -/
theorem member_shape (hf : Fixes π t a rest G0 Ly D) (j : Fin D.mems.length)
    (hlt : (D.mems.get j).id < t.st.oracles.size) :
    ∃ x, t.st.oracles[(D.mems.get j).id]? = some x ∧ (D.mems.get j).sh = x.shape := by
  obtain ⟨x, _, hx, _, hs, _⟩ := member_at hf j hlt
  exact ⟨x, hx, hs⟩

theorem member_shape_first (hf : Fixes π t a rest G0 Ly D) (hmk : t.mask.isSome = true)
    (j : Fin D.mems.length) :
    ∃ x, t.st.oracles[(D.mems.get j).id]? = some x ∧ (D.mems.get j).sh = x.shape :=
  member_shape hf j (member_below_first hf hmk j)

end

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.begun_get
#print axioms VerifiableInference.Desc.K12.Coin.member_at
#print axioms VerifiableInference.Desc.K12.Coin.member_below_first
#print axioms VerifiableInference.Desc.K12.Coin.member_shape_first
#print axioms VerifiableInference.Desc.K12.Coin.begun_size
#print axioms VerifiableInference.Desc.K12.Coin.member_shape
