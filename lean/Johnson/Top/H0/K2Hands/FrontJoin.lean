-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hands/FrontJoin.lean: the code switch's law: «THE TEST ON THE FRONT ACCEPTS», AT
THE FULL SIZE's WRITTEN ENTRY NUMBER i, FROM OTHER FILES' CONCLUSIONS ON THE FRONT fx ITSELF,
each in its own file's letters. A law file; no running text imports it, and no separate root
beside the library stands beneath it.

  frontB2_of_tops   ITS PREMISES, EACH WITH WHOSE THEOREM ENDS IN IT:
    hr hn0 hol   the written entry r and the place's two numbers, at i.
    a1 … a5      the front's codes are cs; its target is the target of sh's group i + 1; its carried
                 rows name sh's two codes and count two mask rows: the walk's tops on the front.
    b            what the carried rows keep, in numbers, is olds: the walk's tops on the kept.
    c1 c2        the front's group is i + 1, and it is there without a row: the walk's count of
                 groups.
    d            the front has n0 messages: the count at the cut.
    C p1 p2 s1   the closing's law on its output, at the front's carried rows, at sh's two code
                 numbers; the codes right behind the closing are cs: the closing's files; the walk.
    w1 w2        cs and sh are the written values: in scope, under the pins.
    e e'         the messages' shapes are the listed ones MW: at the front, and at olds right behind
                 the closing: the fold's fact «msgShapes».
  BY: k2Fronts_at at k2Fronts_full · rowsPub_at · rowsLike_of_kept · test_of_facts.
Limits. Nothing is paid here but the closed half (by the kernel, in FrontsFull.lean and
FrontsFullRows.lean). The full size alone. Nothing on soundness.

-/
import Johnson.Top.H0.K2Hands.FrontsFullRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Hands
open OnBytes
open VerifiableInference.Desc.First.K2Caller (SwRow tableFullLit)
open VerifiableInference.Desc.First.Close (Plan CarriedOk)
open Johnson.G (fxAt)

/-- **The test on the front accepts, at the written entry number i.** -/
theorem frontB2_of_tops {fx : _root_.Tw.K2.Front} {i n0 : ℕ} {olds : List ℕ} {r : SwRow}
    {cs : Codes} {sh : Params.ReqShape} {P : Plan} {G : Group} {S' : Statement}
    (hr : tableFullLit[i]? = some r) (hn0 : n0Full[i + 1]? = some n0)
    (hol : oldsFull[i]? = some olds)
    (a1 : fx.st.codes = cs) (a2 : fx.T = ((reqGroups sh).getD (i + 1) {}).target)
    (a3 : fx.f.rows.code = sh.code) (a4 : fx.f.rows.maskCode = sh.maskCode)
    (a5 : fx.f.rows.masks = 2)
    (b : (switchKept fx.f.rows).toList = olds)
    (c1 : fx.f.group = i + 1) (c2 : ∃ G, fx.st.groups[fx.f.group]? = some G ∧ G.rows = #[])
    (d : fx.st.oracles.size = n0)
    (C : CarriedOk P G S' fx.f.rows) (p1 : P.code = sh.code) (p2 : P.maskCode = sh.maskCode)
    (s1 : S'.codes = cs) (w1 : cs = csW) (w2 : sh = shW)
    (e : ∀ o, o < fx.st.oracles.size → (fx.st.oracles[o]?).map (·.shape) = MW[o]?)
    (e' : ∀ o ∈ olds, (S'.oracles[o]?).map (·.shape) = MW[o]?) :
    ∃ W₀, K2.frameAt (fxAt r) = some W₀ ∧ frontB2 (fxAt r) W₀ (i + 1) 0 n0 olds fx = true := by
  subst w1 w2
  obtain ⟨n0', olds', W₀, g, h1, h2, hW, hg, K, T⟩ := k2Fronts_at k2Fronts_full hr
  obtain rfl := Option.some.inj (hn0.symm.trans h1)
  obtain rfl := Option.some.inj (hol.symm.trans h2)
  obtain ⟨q1, q2, q3⟩ := rowsPub_at hr
  have eg : ((reqGroups shW).getD (i + 1) {}) = g := by
    rw [Array.getD_eq_getD_getElem?, hg]
    rfl
  rw [eg] at a2
  have R : RowsLike fx.f.rows (fxAt r).f.rows W₀ olds :=
    rowsLike_of_kept C b s1 e' (a3.trans q1.symm) (a4.trans q2.symm) (a5.trans q3.symm) K.k1
      (by rw [p1]; exact K.k2) (by rw [p2]; exact K.k3)
  obtain ⟨G₀, hG₀, hrows⟩ := c2
  refine ⟨W₀, hW, test_of_facts ⟨a1.trans K.c1.symm, b, ?_, K.c3, K.c4, by rw [a2]; exact T.shape,
    by rw [a2]; exact T.main, by rw [a2]; exact T.rest, by rw [a2]; exact T.kept, R.code,
    R.maskCode, R.masks, R.keptRows, c1, ⟨G₀, by rw [← c1]; exact hG₀, by rw [hrows]; rfl⟩, d,
    R.tensors, R.d0, R.d1⟩⟩
  rw [K.c2]
  refine List.map_congr_left fun o ho => e o ?_
  rw [d]
  exact K.c3 o ho

end VerifiableInference.Desc.First.K2Hands

#print axioms VerifiableInference.Desc.First.K2Hands.frontB2_of_tops
