--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyDoorShaped.lean: THE DOOR BETWEEN THE KEY FILE's CHAINS ACCEPTS, FROM THE PAIRS, AT THE
THREAD `laid₁` (E2E/KeyRest.lean) AND ANY THREAD OVER THE SHARED CHAIN THAT BEGINS AT THE
DESCRIPTION's START: `DoorYesS`
(Johnson/Desc/ProofFile/Honest/Thread/FileD.lean), at all halves, all tables and ANY two letters for
what is said: IN SCOPE, WHERE THE KEY FITS. Statements with their proofs, by calls. On the
verifier's side alone. NOTHING IS CLAIMED OF ANY PROVER.

`doorYesS_of_two` (E2E/KeyDoorOfEnds.lean) leaves two premises. Here both are paid.
  **`last₁_of_thr`**: THE FIRST: at every thread over the key file's first chain that begins where
    the description starts that chain: where it stands at the border 19, its state has the five
    clauses `Last₁` (E2E/KeyThreadsLaid.lean). By what: the state's shape there is the value of the
  shape's own run (`shape_at`, Johnson/Desc/ProofFile/Honest/Thread/Shape.lean, with
  `carries_whole₁`); in scope that value is the written term T19 (`first_of_sourced`,
    E2E/KeyShapeFullSourced.lean); the five clauses are a test with code on the shape
    (`last₁_of_S`), which accepts T19 by an evaluation in Lean's kernel (`last_full`, both
    E2E/KeyShapeFirstLast.lean). THE SECOND, that the shared chain's last statement has the public
    codes: `codes_of_threads` (E2E/KeySideCash.lean), from both threads' last borders.
  **`doorYesS_laid`**.

Limits.
- IT SAYS: WHERE THE TWO THREADS STAND AT THEIR LAST BORDERS, the third chain's start returns. That
  they stand there is shown nowhere.
- In scope alone: the written terms are the full size's.
- Nothing on what the start returns: that is `start₃_passes` (E2E/KeyStartThird.lean).

-/
import E2E.KeyDoorOfEnds
import E2E.KeyShapeFullSourced
import E2E.KeyShapeFirstLast
import E2E.KeySideCash

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace AtPublicFiles.AtFiles.Full
open OnBytes OnBytes.Params AtPublicFiles.AtFiles AtPublicFiles.KeyShape
open ProofFile.Honest AtPublicFiles.KeyLink
open VerifiableInference.Desc.Key (FirstState Source LaterPlaces)

variable {Z : VerifierAndGoals.PublicFiles} {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces}

/-- **The first chain's last state has what the third chain's start asks of it**, in scope. -/
theorem last₁_of_thr {V W Xh Pb : Type} {Bk : ProverCoinCounts} (hs : KeySourced Z X N P)
    (scope : VerifierAndGoals.InScope Z = true)
    (T₁ : Thread Bk (keyFileDescription X N P).S₁ (keyFileDescription X N P).Cl V W Xh Pb)
    (hbs : T₁.bs = (keyFileDescription X N P).first.blocksInOrder)
    (hbeg : ∀ k w h s₀, T₁.valid w → T₁.begun k w h s₀ → ∃ x, s₀ = (keyFileDescription X N P).start₁ x)
    {k : Coins Bk} {e₁ : (keyFileDescription X N P).S₁} {m : Mid W Xh} {E : Env}
    (h : Thr T₁ 19 k e₁ m E) :
    Last₁ X.chains.made.sized.key.codes X.chains.made.sized.key.once.shape e₁ := by
  obtain ⟨-, hcs, hlin, hlen, hsh0, hrun, hyes, -⟩ :=
    first_of_sourced hs scope fun _ _ _ _ => true
  obtain ⟨bw, hw, he, ha, -⟩ := public_first_sourced hs scope
  have h6 := six_sourced hs scope
  have h19 := shape_at T₁ (Z₁W (pubOf X) CF X.Y.D.1 X.Y.told.1 N fun _ _ _ _ => true) (a₀ := T0)
    (n := 19) (b := 19) (le_of_eq (by rw [hbs, hlen])) (Nat.le_refl _) hyes
    (fun k w h s₀ h1 h2 => by
      obtain ⟨x, rfl⟩ := hbeg k w h s₀ h1 h2
      exact (start₁_shape (cs := CF) (N := N) (X := X) (P := P) _ x).trans hsh0)
    (fun j => by
      rw [hbs]
      exact carries_whole₁ (pubOf X) CF X.Y.D.1 X.Y.told.1 N T₁.ft _ bw hw he ha j) h
  have e19 : sh₁B (pubOf X) CF e₁ = T19 := Except.ok.inj (h19.symm.trans hrun)
  have hL : Last₁ CF (pubOf X).one.lin e₁ :=
    last₁_of_S (pubOf X) CF CF e₁ (by rw [e19, h6.lin]; exact last_full)
  rw [hcs, ← hlin]
  exact hL

end AtPublicFiles.AtFiles.Full

namespace AtPublicFiles.KeyThread
open VerifiableInference.Desc.Key (Xi Source LaterPlaces)
open ProofFile.Honest

/-- **The door accepts at the two threads**: in scope, where the key fits, at a shared thread over
the chain that begins at the description's start. -/
theorem doorYesS_laid {Bk : ProverCoinCounts} {W₀ Rc Cells M Smp Rec X₀' X' : Type} {Z : VerifierAndGoals.PublicFiles}
    {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces}
    (hs : AtPublicFiles.AtFiles.KeySourced Z Xs N Pl) (scope : VerifierAndGoals.InScope Z = true)
    (L : KeyFill Bk W₀ Rc Cells M Smp Rec) (w₀ : W₀) (rc : Rc) (x : Xi)
    (hs₁ : List (Placed (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X'))
    (tb₁ : Fmt.TreeSource → Coins Bk → Local W₀ Rc Xi Unit → List Fmt.Drawn →
    VerifiableInference.Desc.Place × Table)
    (U : Thread Bk (D Xs N Pl).S₂ (D Xs N Pl).Cl Empty (Common W₀ Rc OnBytes.TableKey) X₀'
      OnBytes.TableKey)
    (hO : OverShared Xs N Pl U) (hB : Begun₂ Xs N Pl x U) (hfit : KeyFits Xs x)
    (S₁ : Nat → Coins Bk → Mid (Local W₀ Rc Xi Unit) X' → Prop)
    (S₂ : Nat → Coins Bk → Mid (Common W₀ Rc OnBytes.TableKey) X₀' → Prop) (y : Xi)
    (k : Coins Bk) :
    DoorYesS (D Xs N Pl) (laid₁ Xs N Pl L w₀ rc x hs₁ tb₁) U S₁ S₂ y k :=
  AtPublicFiles.AtFiles.doorYesS_of_two Xs N Pl (laid₁ Xs N Pl L w₀ rc x hs₁ tb₁)
    U S₁ S₂ y k hs.named.plan hO.bs (lengths scope hs.named).2.1
    (fun e₁ m₁ E₁ u => by
      rw [(lengths scope hs.named).1] at u
      exact AtPublicFiles.AtFiles.Full.last₁_of_thr hs scope (laid₁ Xs N Pl L w₀ rc x hs₁ tb₁) rfl
        (fun _ _ _ _ _ hb => ⟨_, hb⟩) u.1)
    fun e₁ m₁ E₁ e₂ m₂ E₂ u₁ u₂ => by
      rw [(lengths scope hs.named).1] at u₁
      rw [(lengths scope hs.named).2.1] at u₂
      exact (codes_of_threads Xs N Pl L w₀ rc x hs scope hfit u₁.1 hO hB u₂.1).2

end AtPublicFiles.KeyThread

#print axioms AtPublicFiles.AtFiles.Full.last₁_of_thr
#print axioms AtPublicFiles.KeyThread.doorYesS_laid
