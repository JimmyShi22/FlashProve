-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/LotEntersFirstCore.lean: THE FIRST CHAIN BEGINS: at a start that ready returns, the first chain's invariant
holds at border 0 at the key file's prover: the library's Enters₁ at the thread T₁ (E2E/FirstHFill.lean). The
proof, with just the premises that it reads.

  `RangeTie Xs K f w₀`: A PREMISE's FORM: where the prover's test on the index says yes, both lookups' sentences
    hold at every witness whose cells are the table of f w₀. K.inRange is a free field of KeyParts: without
    this tie nothing joins it to f. E2E/LotEntersFirstTie.lean pays it at the real value.
  **`entersFirst`**: Enters₁.
  `inRange_of_ready`: where ready returns, the prover's test on the index has said yes: so the premise
    K.inRange w₀ = true of the lot is idle beside «ready returns». `entersFirst_of_ready`: without it.

What is spent. enters₁_of (Honest/Thread/Enters.lean) · the book-keeping's Bool at the first state
(start_shape, Johnson/RunOne/KeyTen.lean) with the written key's ranges in scope (LPFD.one_full) · Side18 at
border 0 (side18_sourced, E2E/KeyStateSide18.lean) · of the four items that are open at border 0: "unmarked"
and pinT are idle at this thread's reading (E2E/FirstHFill.lean's head says so), the two on the range are
RangeTie.

Limits. CONDITIONAL ON «ready returns»: that it does at this prover and the written book is shown nowhere here.
Q.Rel is a letter and a premise: at Rel := False the statement is empty. pinT says nothing here: its content has
its home on the shared chain. One border: nothing on any member's step. The book is any book. Nothing on
soundness, completeness, hiding or binding.
-/
import E2E.FirstHSeat
import E2E.KeyStateSide18
import Johnson.Desc.ProofFile.Honest.Thread.File
import Johnson.Desc.ProofFile.Honest.Thread.Enters
import Johnson.RunOne.KeyTen
import Johnson.Top.Fire.Code.KeyHeldAtName

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace AtPublicFiles.FirstH.Lots
open OnBytes OnBytes.Params
open VerifiableInference.Desc (Wit)
open VerifiableInference.Desc.Key (Xi FirstState Source LaterPlaces KItem)
open Johnson.RunOne.KeyRows1 (meaning₁At start_shape)
open Johnson.Desc.First.Walk.Tied (Reach)
open AtPublicFiles.KeyThread (one₀ side18_sourced)
open AtPublicFiles.KeyFile (KeyParts In1)
open AtPublicFiles.AtFiles (KeySourced)
open VerifierAndGoals (PublicFiles InScope)
open ProofFile.Honest

/-- **Where ready returns, the prover's test on the index has said yes**: it is the fifth of the frame's own
tests. General in the description, the book and the prover. -/
theorem inRange_of_ready {W₀ Rc Xi' Ky Tr X₀ X : Type} {F : VerifiableInference.Desc.FileDescription Xi'} {B : ProverCoinCounts}
    {H : Prover W₀ Rc Xi' Ky Tr X₀ X} {w₀ : W₀} {rc : Rc} {x : Xi'} {c : Coins B}
    {R : Ready W₀ Rc Xi' Ky Tr X₀ X} (h : ready F B H w₀ rc x c = .ok R) : H.inRange w₀ = true := by
  have t := (ready_ok h).1
  unfold readyTests at t
  split at t
  · cases t
  · split at t
    · cases t
    · split at t
      · cases t
      · split at t
        · cases t
        · split at t
          · cases t
          · rename_i hh
            simpa using hh

/-- The written key's lookups' own message has the number 1. -/
theorem messageId_full : Lk6.AtPlan.keyFull.ranges.x.messageId = 1 := by decide +kernel

section
variable {Bk : ProverCoinCounts} {W₀ Rc X₀ X' Wk : Type} (Xs : Source) (N : H2U.PlaceNums) (Pl : LaterPlaces)
  (K : KeyParts W₀ Rc X₀ X' Wk) (f : W₀ → Weights) (Q : LaterFill Bk W₀ Rc) (w₀ : W₀)
  (rc : Rc) (x : Xi)

/-- **The tie of the prover's test on the index to the lookups' sentences**: where the test says yes, the
items inRange 0 and inRange 1 hold at every witness whose cells are the table of f w₀. A premise's form. -/
def RangeTie : Prop :=
  K.inRange w₀ = true → ∀ l, l < 2 → ∀ v : Wit HCells Unit HTab,
    v.cells = cellsOf (one₀ Xs).lin (f w₀) → (meaning₁At (one₀ Xs) readH).inRange l v

/-- **The first chain begins.** -/
theorem entersFirst {Z : PublicFiles} (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    (tie : RangeTie Xs K f w₀) (rel : Q.Rel w₀ rc x) (inR : K.inRange w₀ = true) (k : Coins Bk)
    (R : Ready W₀ Rc Xi OnBytes.TableKey Unit X₀ X')
    (hR : ready (AtPublicFiles.AtFiles.keyFileDescription Xs N Pl) Bk (AtPublicFiles.KeyFile.keyProver K) w₀ rc x k = .ok R) :
    Enters₁ (AtPublicFiles.AtFiles.keyFileDescription Xs N Pl) (AtPublicFiles.KeyFile.keyProver K) (Th Xs N Pl K f Q w₀ rc x) w₀ rc x k
      R := by
  obtain ⟨-, ⟨⟩, -, hown, -⟩ := ready_ok hR
  obtain ⟨Y₀, m, h0, hm, hX, -, -⟩ := hs.source
  obtain ⟨e1, e2, -⟩ := LPFD.one_full (N := N) (P := Pl) scope
    (Johnson.RunOne.Law.ReadAtO.readOf_publicOfO h0) hm hX hs.named.plan
  obtain ⟨x₀, x₁, h2⟩ := LPFD.hl_in_scope (N := N) (P := Pl) scope
    (Johnson.RunOne.Law.ReadAtO.readOf_publicOfO h0) hm hX hs.named.plan
  refine enters₁_of hR (fun _ => rfl) rfl rfl rfl ⟨?_, ?_, (), rfl⟩ ?_ trivial ⟨hown, rel⟩
  · exact start_shape (one₀ Xs) (by rw [h2]; rfl) (by rw [e1]; exact messageId_full)
  · exact side18_sourced Xs N Pl hs scope 0 0 (x, _) (Nat.zero_le _) (Reach.zero x)
  · intro ds (i : KItem) (hi : i ∈ [KItem.unmarked, KItem.pinT, KItem.inRange 0, KItem.inRange 1])
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact rfl
    · exact ⟨(), rfl, trivial⟩
    · exact tie inR 0 (by decide) _
        (congrArg (fun w : In1 W₀ Rc => cellsOf (one₀ Xs).lin (f w.w₀)) hown)
    · exact tie inR 1 (by decide) _
        (congrArg (fun w : In1 W₀ Rc => cellsOf (one₀ Xs).lin (f w.w₀)) hown)

/-- The same without the premise on the prover's test, which «ready returns» holds. -/
theorem entersFirst_of_ready {Z : PublicFiles} (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    (tie : RangeTie Xs K f w₀) (rel : Q.Rel w₀ rc x) (k : Coins Bk)
    (R : Ready W₀ Rc Xi OnBytes.TableKey Unit X₀ X')
    (hR : ready (AtPublicFiles.AtFiles.keyFileDescription Xs N Pl) Bk (AtPublicFiles.KeyFile.keyProver K) w₀ rc x k = .ok R) :
    Enters₁ (AtPublicFiles.AtFiles.keyFileDescription Xs N Pl) (AtPublicFiles.KeyFile.keyProver K) (Th Xs N Pl K f Q w₀ rc x) w₀ rc x k
      R :=
  entersFirst Xs N Pl K f Q w₀ rc x hs scope tie rel (inRange_of_ready hR) k R hR

end

end AtPublicFiles.FirstH.Lots

#print axioms AtPublicFiles.FirstH.Lots.inRange_of_ready
#print axioms AtPublicFiles.FirstH.Lots.entersFirst_of_ready
#print axioms AtPublicFiles.FirstH.Lots.messageId_full
#print axioms AtPublicFiles.FirstH.Lots.entersFirst
