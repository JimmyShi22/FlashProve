-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/RowsSay.lean: the code switch: THE SECOND CLAUSE OF WHAT STANDS BEHIND
(`RowsHoldT`, Johnson/Top/H0/K2Hands/TieT.lean: every row that the switch's group has gained holds
of the new messages) FROM WHAT THESE ROWS SAY OF WORDS. For the tie between the law's relation
behind and the table of joints' item on a class of rows.

Main names:
  `rowsHoldT_of_says`: by `says_iff_textHolds` (SaysText.lean), row by row.
Limits. Its four premises (the words are the typed messages at the typed entries' names; each gained
row says its claim and meets `OnlyAt`; the names lie in the tables behind; the words are 0 outside
`inside`) are shown by nobody here. Nothing on soundness. On hiding nothing.

-/
import Johnson.Top.H0.K2Caller.SaysText
import Johnson.Top.H0.K2Hands.TieT

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice Cb Iop IOR Johnson.Pack Johnson.Top.H OnBytes.Tie.Pv.Switch
open OnBytes.Means (Words Says)
open VerifiableInference.Desc.First.K2Hands

variable {S : Sig GE} (R : RowsK S) [Nonempty R.G.P] {kp : S.O → Prop} [DecidablePred kp]
  (Hd : GHeld R.Sh kp) {B Kc St₀ Wp : Type} [Fintype B] (Sb : B → Type)
  (sl : ∀ b, Slf GE (Sb b) R.G.C.J) (Z : Evader GE (R.G.Row B)) {E₀ : ExtSpec}
  (A₀ : Rels Kc St₀ E₀ ((S.sub kp).Msg × Wp))
  (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ))
  (iJ : R.Sh.Cf.J → (sigOf cs l).Ent) (iQ : R.Sh.Cf.Q → (sigOf cs l).Ent)
  (t : ℕ) (w₀ : (Hd.foldD Sb sl Z A₀).tgt.W) (p : K2.P2)

set_option quotPrecheck false in
local notation "LocK" => (closeSel Hd Sb sl Z A₀ cs l iJ iQ t w₀).loc

/-- **THE SECOND CLAUSE OF WHAT STANDS BEHIND THE SWITCH, FROM WHAT THE ROWS SAY OF WORDS.** s, s':
    the
verifier's state in front and behind; u: the typed messages; m: words. hm: at the new sending's
    typed
entries the words are u's · hrow: each row that the switch's group has gained says its claim of the
words, and has no coefficient inside the tables but at a typed entry · hF: the typed entries lie in
the tables behind · h0: outside `inside` the words are 0. -/
theorem rowsHoldT_of_says (s s' : Rec) (u : (LocK).S.Msg) (m : Words GE)
    {inside : ℕ → Part → ℕ → Prop}
    (hm : ∀ fx, K2.frontAt p s = some fx → ∀ n : (sigOf cs l).Ent,
      (LocK).S.ents u (newEnt R Hd Sb sl Z A₀ cs l iJ iQ t w₀ n) =
        m (fx.st.oracles.size + (entAt cs l n).1) (entAt cs l n).2.1 (entAt cs l n).2.2)
    (hrow : ∀ fx, K2.frontAt p s = some fx → ∀ G0 G', fx.st.groups[fx.f.group]? = some G0 →
      s'.st.groups[fx.f.group]? = some G' → ∀ r ∈ G'.rows.toList.drop G0.rows.size,
        Says rdE s'.st r m ∧ OnlyAt cs l (fun i => fx.st.oracles.size + i) inside r)
    (hF : ∀ fx, K2.frontAt p s = some fx →
      ∀ n, nameOf cs l (fun i => fx.st.oracles.size + i) n ∈ tabAll s'.st)
    (h0 : ∀ x ∈ tabAll s'.st, ¬ inside x.1 x.2.1 x.2.2 → m x.1 x.2.1 x.2.2 = 0) :
    RowsHoldT R Hd Sb sl Z A₀ cs l iJ iQ t w₀ p s s' u := by
  intro fx hfx G0 G' g0 g1 r hr
  obtain ⟨hs, ho⟩ := hrow fx hfx G0 G' g0 g1 r hr
  have e : (fun n => (LocK).S.ents u (newEnt R Hd Sb sl Z A₀ cs l iJ iQ t w₀ n)) =
      fun n => m (fx.st.oracles.size + (entAt cs l n).1) (entAt cs l n).2.1 (entAt cs l n).2.2 :=
    funext (hm fx hfx)
  rw [e]
  exact (says_iff_textHolds cs l (fun i => fx.st.oracles.size + i)
    (fun a b h => Nat.add_left_cancel h) ho s'.st m (hF fx hfx) h0).1 hs

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.rowsHoldT_of_says
