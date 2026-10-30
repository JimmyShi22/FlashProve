-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/LooksK2.lean: THE CODE SWITCH (kind K2) AND THE HEAD's LINK's MAKER:
THEIR
SHARES OF THE WALK OF Johnson/Desc/First/Link/Law/LooksWalk.lean («the ledger's arrays have the
plan's
shapes»). Theorems: CALLS INTO THE SWITCH's FILES' LAWS.

  `k2_link_kept`: a yes of the switch's decision leaves the reading of the open link's context, at
    each of the three sorts of place (`fork_kept`, Johnson/Top/H0/Tw/K2C/ForkKept.lean, proof for
    proof, at the other reading).
  `k2_keeps`, `k2_steps`: **(codeSwitchKind p).Steps (KeepsLooks shOf)**: with `fork_kept`.
  `placeH2_makes`: **THE HEAD's LINK's MAKER: the whole place «H:2» (the switch, then the step
  without
    a round that opens the link)**: behind it the open ledger is laid off the plan's arrays
    (`placeH2_fork`, K2C/HeadLedger.lean) and the open link has the number P.l (`placeH2_frame`,
    K2C/HeadNumbers.lean): UNDER ONE PREMISE ON THE PLAN: `shOf P.l` is the looks of P.X.Fp's
    arrays.
Limits. The decisions alone. That the IOP's own sub-protocols at these places stand under these is
the seats' tie. Nothing on soundness.
-/
import Johnson.Desc.First.Link.Law.LooksFrame
import Johnson.Top.H0.Tw.K2C.ForkKept
import Johnson.Top.H0.Tw.K2C.HeadLedger
import Johnson.Top.H0.Tw.K2C.HeadNumbers

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2

/-- A yes of the switch's decision leaves the reading of the open link's context. -/
theorem k2_link_kept {snd : _root_.Tw.K2.SendFn} {p : P2} {s : S} {rs : List Fmt.RoundView}
    {gs : List (List (ℕ × List UInt64))} {s' : S} (h : decideWith snd p s rs gs = .ok s') :
    s'.link? = s.link? := by
  rcases (stands _ _ _ _ _ _ h) with ⟨hp, _⟩ | ⟨hp, _⟩ | ⟨hp, _⟩
  · obtain ⟨r₁, r₂, x, w, roots, S', f, mine, _, k⟩ := link_inv hp h
    rw [k.hOut]
    rfl
  · obtain ⟨r₁, r₂, a, G, w, roots, _, k⟩ := head_inv hp h
    rw [k.hOut]
    simp [S.link?, k.hHere]
  · obtain ⟨r₁, r₂, a, G, w, roots, _, k⟩ := finish_inv hp h
    rw [k.hOut]
    simp [S.link?, k.hHere]

theorem k2_keeps (shOf : ℕ → List Look) {snd : _root_.Tw.K2.SendFn} {p : P2} {s : S}
    {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))} {s' : S}
    (h : decideWith snd p s rs gs = .ok s') : KeepsLooks shOf s s' :=
  keeps_same shOf (fork_kept h) (by rw [k2_link_kept h])

/-- **K2: the code switch.** -/
theorem k2_steps (shOf : ℕ → List Look) (p : P2) :
    (codeSwitchKind p : Block S Unit).Steps (KeepsLooks shOf) := by
  intro s rs gs s' h
  exact k2_keeps shOf (show decideWith _ p s rs gs = .ok s' from h)

/-- **THE HEAD's LINK's MAKER: the whole place «H:2».** -/
theorem placeH2_makes (shOf : ℕ → List Look) (p : P2) (n : String) (P : HeadPar)
    (hsh : shOf P.l = P.X.Fp.trees.toList.map look) :
    ((codeSwitchKind p : Block S Unit).andThen n (headOpened n p.place P)).Steps (KeepsLooks shOf) := by
  intro s rs gs s' h
  obtain ⟨_, _, _, L, _, hL, hl, _⟩ := placeH2_frame h
  exact keeps_laid shOf { trees := P.X.Fp.trees } P.hp.ns L (placeH2_fork h) hL (by rw [hl]; exact
      hsh)

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.k2_link_kept
#print axioms VerifiableInference.Desc.LinkJoin.k2_keeps
#print axioms VerifiableInference.Desc.LinkJoin.k2_steps
#print axioms VerifiableInference.Desc.LinkJoin.placeH2_makes
