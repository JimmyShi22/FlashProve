-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Rows/Parts.lean: FROM SEVEN WALKS AND ONE CLOSED FACT ON THE TAIL TO
«rowsFrom RETURNS». Theorems. A law file; no running text imports it.
  `twinsAt c o n A`   the seven chains, each with the calls of its routine run once from nothing.
  `calls_of_goods`    seven `Good`: callsFrom returns these seven.
  `like_twins`        the seven at two tables of arms say the same of samples, where «proof 0»
                      returns at both.
  `rows_of_parts` seven `Good` · the routine of «proof 0» at ANOTHER table of arms A' ends at
                  counters 0 · the tail returns at the seven twins at A': rowsFrom returns at A.
SUPERSEDED IN USE: like_twins and rows_of_parts (a twin at another table of arms) are called by
nothing: Twin.lean's rows_of_partsL (twins without arms) has taken their place; twinsAt · seven_oks
· calls_of_goods are in use.
Limits. Every premise of rows_of_parts is owed: NO CLOSED FACT IS HERE. Nothing on soundness or on
hiding.
-/
import Johnson.AtFull.Rows.Tail

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Params
open Johnson.G hiding sendsFrom
open VerifiableInference.Number (sendsFrom)

/-- The seven chains, each with the calls of its routine run once from nothing. -/
def twinsAt (c : Configured) (o : List Nat) (n : Nat) (A : Nat → Arm) : List Johnson.G.Chain :=
  [twinOf c.sized.set "key" 0 .once (key0R c),
   twinOf c.sized.set "key" 1 (scOf c.sized.key.once .shared) (key1R c),
   twinOf c.sized.set "key" 2 (scOf c.sized.key.once .request) (key2R c),
   twinOf c.sized.set "entry" 0 .once (entryR c),
   twinOf c.sized.set "proof" 0 .request (proof0R c o n A),
   twinOf c.sized.set "proof" 1 (scOf c.sized.proof.batch .shared) (proof1R c),
   twinOf c.sized.set "proof" 2 (scOf c.sized.proof.batch .request) (proof2R c)]

theorem seven_oks {ε α β : Type} {e0 e1 e2 e3 e4 e5 e6 : Except ε α} {a0 a1 a2 a3 a4 a5 a6 : α}
    (b : β)
    (h0 : e0 = .ok a0) (h1 : e1 = .ok a1) (h2 : e2 = .ok a2) (h3 : e3 = .ok a3) (h4 : e4 = .ok a4)
    (h5 : e5 = .ok a5) (h6 : e6 = .ok a6) :
    ([e0, e1, e2, e3, e4, e5, e6].mapM id >>= fun l => (pure (b, l) : Except ε (β × List α))) =
      .ok (b, [a0, a1, a2, a3, a4, a5, a6]) := by
  subst h0 h1 h2 h3 h4 h5 h6
  have e := mapM_id_oks (ε := ε) [a0, a1, a2, a3, a4, a5, a6]
  simp only [List.map_cons, List.map_nil] at e
  rw [e]
  rfl

theorem calls_of_goods {c : Configured} {o : List Nat} {n : Nat} {A : Nat → Arm}
    {k0 k1 k2 p0 p1 p2 : Planned}
    (hk : c.key = [k0, k1, k2]) (hp : c.proof = [p0, p1, p2])
    (g0 : Good c.sized.set k0.rounds (⟨.once, 0, 0, 0⟩, 0) (key0R c))
    (g1 : Good c.sized.set k1.rounds (⟨scOf c.sized.key.once .shared, 0, 0, 0⟩, 0) (key1R c))
    (g2 : Good c.sized.set k2.rounds (⟨scOf c.sized.key.once .request, 0, 0, 0⟩, 0) (key2R c))
    (g3 : Good c.sized.set c.entry.rounds (⟨.once, 0, 0, 0⟩, 0) (entryR c))
    (g4 : Good c.sized.set p0.rounds (⟨.request, 0, 0, 0⟩, 0) (proof0R c o n A))
    (g5 : Good c.sized.set p1.rounds (⟨scOf c.sized.proof.batch .shared, 0, 0, 0⟩, 0) (proof1R c))
    (g6 : Good c.sized.set p2.rounds (⟨scOf c.sized.proof.batch .request, 0, 0, 0⟩, 0)
      (proof2R c)) :
    callsFrom c o n A = .ok (c.sized.set, twinsAt c o n A) :=
  (callsFrom_eq (o := o) (n := n) (A := A) hk hp).trans
    (seven_oks c.sized.set
      (one_twin (faith_key0R c) g0).2 (one_twin (faith_key1R c) g1).2
          (one_twin (faith_key2R c) g2).2
      (one_twin (faith_entryR c) g3).2 (one_twin (faith_proof0R c o n A) g4).2
      (one_twin (faith_proof1R c) g5).2 (one_twin (faith_proof2R c) g6).2)

theorem like_twins {c : Configured} {o : List Nat} {n : Nat} {A A' : Nat → Arm} {p0 : Planned}
    {sc' : Scope}
    (g4 : Good c.sized.set p0.rounds (⟨.request, 0, 0, 0⟩, 0) (proof0R c o n A))
    (t4 : endOf c.sized.set ⟨.request, 0, 0, 0⟩ (proof0R c o n A') = some ⟨sc', 0, 0, 0⟩) :
    List.Forall₂ Like (twinsAt c o n A) (twinsAt c o n A') := by
  obtain ⟨⟨P4, n4⟩, _⟩ := one_twin (file := "proof") (ch := 0) (faith_proof0R c o n A) g4
  have r4 := runs_of_end (fr_proof0R c o n A') t4
  have key : Like (twinOf c.sized.set "proof" 0 .request (proof0R c o n A))
      (twinOf c.sized.set "proof" 0 .request (proof0R c o n A')) :=
    ⟨(rfl : "proof" = "proof"), (rfl : (0 : Nat) = 0),
        noted_trace (proof0R_sim c o n A A') n4 (noted_of_runs r4)⟩
  exact .cons (like_refl _) (.cons (like_refl _) (.cons (like_refl _) (.cons (like_refl _)
      (.cons key (.cons (like_refl _) (.cons (like_refl _) .nil))))))

/-- **From seven walks and one closed fact on the tail: the second reading's text returns.** -/
theorem rows_of_parts {c : Configured} {o : List Nat} {n : Nat} {A A' : Nat → Arm}
    {k0 k1 k2 p0 p1 p2 : Planned} {sc' : Scope}
    (hk : c.key = [k0, k1, k2]) (hp : c.proof = [p0, p1, p2])
    (g0 : Good c.sized.set k0.rounds (⟨.once, 0, 0, 0⟩, 0) (key0R c))
    (g1 : Good c.sized.set k1.rounds (⟨scOf c.sized.key.once .shared, 0, 0, 0⟩, 0) (key1R c))
    (g2 : Good c.sized.set k2.rounds (⟨scOf c.sized.key.once .request, 0, 0, 0⟩, 0) (key2R c))
    (g3 : Good c.sized.set c.entry.rounds (⟨.once, 0, 0, 0⟩, 0) (entryR c))
    (g4 : Good c.sized.set p0.rounds (⟨.request, 0, 0, 0⟩, 0) (proof0R c o n A))
    (g5 : Good c.sized.set p1.rounds (⟨scOf c.sized.proof.batch .shared, 0, 0, 0⟩, 0) (proof1R c))
    (g6 : Good c.sized.set p2.rounds (⟨scOf c.sized.proof.batch .request, 0, 0, 0⟩, 0) (proof2R c))
    (t4 : endOf c.sized.set ⟨.request, 0, 0, 0⟩ (proof0R c o n A') = some ⟨sc', 0, 0, 0⟩)
    (ht : (tailFrom c c.sized.set (twinsAt c o n A')).toOption.isSome = true) :
    (rowsFrom c o n A).toOption.isSome = true := by
  rw [rowsFrom_eq (calls_of_goods hk hp g0 g1 g2 g3 g4 g5 g6),
    tail_congr c c.sized.set (like_twins g4 t4)]
  exact ht

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.seven_oks
#print axioms VerifiableInference.Desc.LinkJoin.calls_of_goods
#print axioms VerifiableInference.Desc.LinkJoin.like_twins
#print axioms VerifiableInference.Desc.LinkJoin.rows_of_parts
