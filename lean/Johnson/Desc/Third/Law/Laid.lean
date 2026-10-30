-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Third/Law/Laid.lean: the yes of K14's second part of the last chain gives `Laid`
(Johnson/Desc/Third/Law/LaidDef.lean). Theorems.

Main names:
  `laid_k14Second`: the block's yes gives a border, Omega's record there, the own group in front and
    the row (Dot), with all of `Laid`'s fields: by `says_k14Second`, `sharp_k14Second`,
    `bookSays_k14Second`, `linDotRow_plain`, `dotIn_k14Second`, `inOrder_k14Second` and
    `alone_k14Second`.
  `laid_irrefl`: `Laid` holds of no record and itself. So the block that says yes to all and hands
    the record on does not give it. The block that says no to all gives it, as it gives whatever
    is stated in the form "a yes gives": that this block does say yes is shown by a run on honest
    files, not by a law.

Limits. Those of the six laws. Nothing on soundness or on hiding.
-/
import Johnson.Desc.Third.Law.LaidDef
import Johnson.Desc.Third.Law.Sharp
import Johnson.Desc.Third.Law.DotIn
import Johnson.Desc.Third.Law.Order
import Johnson.Desc.Third.Law.Alone

set_option autoImplicit false
set_option relaxedAutoImplicit false

open OnBytes

namespace VerifiableInference.Desc.Third.Law

/-- **The block's yes gives Laid.** -/
theorem laid_k14Second {Cl : Type} (p : P₁₄) (s s' : S₃) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (h : (batchLinearConstraintsSecondPart (Cl := Cl) p).decide s rs gs = .ok s') :
    ∃ b y G dot, Laid p.S s s' b y G dot := by
  obtain ⟨b, y, G, dot, c1, c2, c3, c4, c5, c6, c7, c8, c9, _, c11, c12, f1, f2, f3⟩ :=
    says_k14Second p s s' rs gs h
  obtain ⟨r1, r2, r3, r4⟩ := sharp_k14Second p s s' rs gs h
  obtain ⟨bx, q, t, q', hbx, hq, ht, hstep, hq', _, ⟨tO, htO, hn, hsr⟩, fp, ft⟩ :=
    bookSays_k14Second p s s' rs gs h
  have eb : bx = b := Option.some.inj (hbx.symm.trans c1)
  rw [eb] at hq ht
  have eq' : q' = (s.book.trees.size, 0) := Option.some.inj (hq'.symm.trans r4)
  rw [eq'] at htO
  obtain ⟨q2, t2, hq2, ht2, hone⟩ := alone_k14Second p s s' rs gs h b c1
  have eq2 : q2 = q := Option.some.inj (hq2.symm.trans hq)
  rw [eq2] at ht2
  have et : t2 = t := Option.some.inj (ht2.symm.trans ht)
  rw [et] at hone
  obtain ⟨b2, G2, dot2, hb2, hG2, hd2, hin⟩ := dotIn_k14Second p s s' rs gs h
  have e1 : b2 = b := Option.some.inj (hb2.symm.trans c1)
  rw [e1] at hd2
  have e2 : G2 = G := Option.some.inj (hG2.symm.trans c7)
  have e3 : dot2 = dot := Option.some.inj (hd2.symm.trans c9)
  rw [e2, e3] at hin
  exact ⟨b, y, G, dot, c1, c2, c3, c4, c5, c6, c7, c8, c9, linDotRow_plain _ _ _ _ _ _ _ _ c9, c11,
    hin, c12, f1, f2, f3, r1, r2, hstep, r4, fp, r3, ft, ⟨q, t, tO, hq, ht, hone, htO, hn, hsr⟩,
    fun hI hO => inOrder_k14Second p s s' rs gs h b c1 hI hO⟩

/-- Laid holds of no record and itself: the book has one tree more behind. -/
theorem laid_irrefl (S : Params.LinShape) (s : S₃) (b : Border) (y : OnBytes.Oracle)
    (G : OnBytes.Group) (dot : OnBytes.Row) : ¬ Laid S s s b y G dot := by
  intro h
  have t := h.trees
  omega

end VerifiableInference.Desc.Third.Law
