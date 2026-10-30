-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/K3X/HeadTests.lean: what the two lookups of the output head's link (link 24 of the
proof's first chain) ask of the public data (SixAt, Johnson/AtFull/K3X/SixAt.lean), as tests with
code on the head's layout and plan; and that a yes of these tests gives the six statements.
Definitions and one general law; nothing is evaluated here.

Why. Two of the things that the six statements read at this link are not asked of Lean's kernel at
the full size: the head's nine counts of padding keys (the layout's fs.pub) and the host's own count
(laidHead): both walk over up to 262,144 columns a call and read arrays made by single writes;
whether the kernel would bear them was not measured. They are paid by laws
(Johnson/AtFull/Head/PubAtFull.lean, Johnson/AtFull/K3X/HeadLaidAtFull.lean) and enter here as
premises. All else is small: the tests below gather it.

  namesHeadT     the names that lookAt gives the link's two lookups are the written names.
  headCallsT HLy the layout's six calls, their tables taken out, are the written calls.
  headTailT ns tl  of the head's plan: its number of slots; of its smallness test's record tl: the
                 two calls of the lookup on the digits, its counts, its depth limit, its first slot
                 (the link's slots, less the slots of the step on the weights that follows at 2^18
                 columns, less the lookup's own), the host's count, the test on the padding key; and
                 that the map of the arrays has the vector of reads, which the caller's readers ask.
  **six_head**   at a public part with profile 4 and twelve groups: a yes of the three tests, two
                 numbers of the shape, the two premises on the counts, and that the weights' matrix
                 has 2^18 columns, give SixAt X 24.

Limits. That a test says yes at any public data is not said here. The two premises on the counts are
premises. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.K3X.KernelTests

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.K3X

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.K3 (quietAt isHead)
open VerifiableInference.Desc.First.Look (lookAt laidAt tlAt padKeyAt laidDigits padKeyDigits
  laidHead digitsNext)
open Johnson.AtFull.ProofRows.K3 (strip)
open Johnson.AtFull.Lots.K3 (pubW sortOf quietW callerW nameW callsW firstW nsW lmW)
open Johnson.AtFull.Lots.K3.Light (viewOf viewW sameCall sameList)

/-- The names at the head's link are the written ones. -/
def namesHeadT : Bool := [false, true].all fun d => nameOf 24 "head" d == nameW 24 d

/-- The head's six calls, their tables taken out. -/
def headCallsT (HLy : Head.HL) : Bool :=
  sameList (HLy.cl.map strip).toList (callsW 3 false).toList

/-- What is read of the head's plan. -/
def headTailT (ns : Nat) (tl : HTailF2) : Bool :=
  ns == nsW 3 && sameList [tl.z1.call, tl.z2.call] (callsW 3 true).toList &&
    tl.f9.pub == pubW 3 true && tl.lidb == 28 &&
    digitsNext ns (wsForkSlots 18) (Forest.elems tl.f9) == some (firstW 3 true) &&
    laidDigits tl == some (pubW 3 true) && padKeyDigits tl && (tl.ix.U.getD 2 none).isSome

theorem names_head_at (h : namesHeadT = true) (d : Bool) : nameOf 24 "head" d = nameW 24 d :=
  beq_iff_eq.1 (List.all_eq_true.1 h d (by cases d <;> simp))

/-- **The six at the output head's link.** -/
theorem six_head {X : Verify.Public} (h4 : X.p4 = true) (hN : X.NGr = 12) (hn : namesHeadT = true)
    (l1 : X.hS.LIDB = 28) (m1 : X.hS.lmbH = 15) (hc : headCallsT X.HLy = true)
    (p1 : X.HLy.fs.pub = pubW 3 false) (q1 : laidHead X.hS X.HLy = some (pubW 3 false))
    (hk : X.layers.wsLay.lk = 18) (ht : headTailT X.H.ns X.H.tl = true) : SixAt X 24 := by
  have c1 : X.HLy.cl.map strip = callsW 3 false := Array.toList_inj.1 (sameList_eq hc)
  simp only [headTailT, Bool.and_eq_true, beq_iff_eq] at ht
  obtain ⟨⟨⟨⟨⟨⟨⟨s1, c0⟩, p2⟩, l2⟩, n2⟩, q2⟩, k2⟩, u2⟩ := ht
  have c2 : #[X.H.tl.z1.call, X.H.tl.z2.call] = callsW 3 true :=
    Array.toList_inj.1 (sameList_eq c0)
  have nm := names_head_at hn
  have w5 : ∀ d, quietW 24 d = d := fun d => by cases d <;> rfl
  have w6 : callerW 24 = true := rfl
  have t1 : tlAt X 24 = some X.H.tl := by
    simp only [tlAt, h4, hN, ↓reduceIte, Nat.reduceMul, beq_self_eq_true]
  refine ⟨?_, ?_, fun d => ?_, fun d => ?_, fun d => ?_, ?_⟩
  · refine ⟨{ name := nameOf 24 "head" false, link := 24, calls := X.HLy.cl, pub := X.HLy.fs.pub
              lid := X.hS.LIDB, base := ({ trees := X.H.Fp.trees } : Fork).fillL
              F := (({ trees := X.H.Fp.trees } : Fork).fillL).slots X.H.ns, fs := X.HLy.fs
              ns := X.H.ns, lm := X.hS.lmbH }, ?_, ?_⟩
    · simp only [lookAt, h4, hN, ↓reduceIte, Nat.reduceMul, beq_self_eq_true, Bool.false_eq_true]
      rfl
    · exact view_of_fields true (nm false) rfl c1 p1 l1 rfl s1 m1
  · refine ⟨{ name := nameOf 24 "head" true, link := 24
              calls := #[X.H.tl.z1.call, X.H.tl.z2.call], pub := X.H.tl.f9.pub
              lid := X.H.tl.lidb, base := ({ trees := X.H.Fp.trees } : Fork).fillL
              F := { (({ trees := X.H.Fp.trees } : Fork).fillL).slots X.H.ns with
                next := firstW 3 true }
              fs := X.H.tl.f9, ns := X.H.ns, lm := 5 }, ?_, ?_⟩
    · simp only [lookAt, h4, hN, ↓reduceIte, Nat.reduceMul, beq_self_eq_true, hk, n2,
        Option.map_some]
      rfl
    · exact view_of_fields false (nm true) rfl c2 p2 l2 rfl s1 rfl
  · cases d
    · have e : laidAt X 24 false = laidHead X.hS X.HLy := by
        simp only [laidAt, h4, hN, ↓reduceIte, Nat.reduceMul, beq_self_eq_true, Bool.false_eq_true]
      rw [e, q1]
      rfl
    · have e : laidAt X 24 true = laidDigits X.H.tl := by
        simp only [laidAt, t1, ↓reduceIte, Option.bind_some]
      rw [e, q2]
      rfl
  · cases d
    · simp only [padKeyAt, h4, hN, ↓reduceIte, Nat.reduceMul, beq_self_eq_true, Bool.false_eq_true]
    · simp only [padKeyAt, t1, ↓reduceIte, Option.map_some, k2]
  · rw [w5]
    cases d <;>
      simp only [quietAt, isHead, h4, hN, ↓reduceIte, Nat.reduceMul, beq_self_eq_true,
        Bool.false_eq_true, Option.isSome_some, Option.isSome_none]
  · rw [w6]
    simp only [K3Lot.readersAt, isHead, h4, hN, ↓reduceIte, Nat.reduceMul, beq_self_eq_true,
      Option.isSome_map, u2]

end Johnson.AtFull.K3X

#print axioms Johnson.AtFull.K3X.names_head_at
#print axioms Johnson.AtFull.K3X.six_head
