-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/SwitchSel.lean: the caller of the code switch at which the open word's message and
randomness are chosen entries of the new messages: a value at which the library's theorems on what
a switch leaves open apply.

Johnson/Top/H/SwitchVec.lean has the caller `switchVec`, in which the reading `cutN` of the open
word's message and randomness off the new messages is a letter. In the programs every entry of the
old message and of its randomness lies at a place in a new message. Here `cutN` is made of two maps
of names. Nothing new is proved: `lin_loc` (Johnson/Top/H/AfterLay.lean) gives the condition
`LdLocD.Lin`, and `ldLoc_after_rows` (Cb/Req1/LdSegAfterRows.lean) then says that what is claimed
behind the positions is a family of rows on the entries of the open messages. How these rows are
laid into the link's own closing: `after_of_rows`, `rowLay_ok_after` (Johnson/Top/H/AfterLay.lean).
The library's own cut by places, for its standard new messages: Cb/Ld/LdGroupPlace.lean.
Definitions, statements and proofs.
Main names:
  `cutSel iJ iQ`: the reading made of iJ and iQ: which entry of which new message holds an entry of
    the open word's message, of its randomness.
  `closeSel`: the second half of the closing at that reading. `switchSel`: the caller.
  `switchSel_loc`: the caller's record of the positions is `closeSel.loc`, by definition.
  `switchSel_ok`: the kind's condition, from the three premises of `switchOf_ok`.
  `sel_lin`: `LdLocD.Lin` there, under the laws of the folded complex's code: a call of `lin_loc`.
  `after_sel`: `LdLocD.After` holds exactly where all rows of `LdLocD.rowsOf` hold of the entries:
    a call of `ldLoc_after_rows`.
Limits: iJ and iQ are letters; nothing says that they are the programs' places, and nothing asks
that they are one to one. Those of the files named.

-/
import Johnson.Top.H.SwitchVec
import Johnson.Top.H.AfterLay

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Top.H
open OnBytes.Slice Cb Iop IOR Johnson.Pack
open VerifiableInference.OnPublicFiles.RowsOf (lin_loc)

variable {S : Sig GE} {G : Grp S} [Nonempty G.P] {Sh : GShape G} {kp : S.O → Prop}
  [DecidablePred kp] (Hd : GHeld Sh kp) {B Kc St₀ Wp : Type} [Fintype B] (Sb : B → Type)
  (sl : ∀ b, Slf GE (Sb b) G.C.J) (Z : Evader GE (G.Row B)) {E₀ : ExtSpec}
  (A₀ : Rels Kc St₀ E₀ ((S.sub kp).Msg × Wp))
  (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ))
  (iJ : Sh.Cf.J → (sigOf cs l).Ent) (iQ : Sh.Cf.Q → (sigOf cs l).Ent)
  (t : ℕ) (w₀ : (Hd.foldD Sb sl Z A₀).tgt.W) {Pw : Type} (Cw : LdCode GE Pw)

/-- The open word's message and randomness, as chosen entries of the new messages. -/
noncomputable def cutSel (n : (sigOf cs l).Msg) : Sh.Cf.N.Wit :=
  (fun j => (sigOf cs l).ents n (iJ j), fun q => (sigOf cs l).ents n (iQ q))

/-- The second half of the closing at that reading. -/
noncomputable def closeSel : LdCloseD (vecD (Hd.foldD Sb sl Z A₀)) :=
  closeVec _ (closeOf Hd Sb sl Z A₀ cs l (cutSel cs l iJ iQ) t w₀)

/-- The caller at that reading. -/
noncomputable def switchSel : Cb.Pv.SendLocRide.Size GE :=
  switchVec Hd Sb sl Z A₀ cs l (cutSel cs l iJ iQ) t w₀ Cw

/-- The caller's record of the positions. -/
theorem switchSel_loc :
    Cb.Pv.SendLoc.loc (switchSel Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw).sw =
      (closeSel Hd Sb sl Z A₀ cs l iJ iQ t w₀).loc := rfl

/-- The kind's condition. -/
theorem switchSel_ok (h : allMeet cs l = true) (hL : Hd.Laws) (hF : G.Fits) :
    Cb.Pv.SendLocRide.OK (switchSel Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw) :=
  switchVec_ok Hd Sb sl Z A₀ cs l (cutSel cs l iJ iQ) t w₀ Cw h hL hF

/-- The condition under which what is claimed behind the positions is a family of rows. -/
theorem sel_lin (hC : Sh.Cf.Laws) :
    (closeSel Hd Sb sl Z A₀ cs l iJ iQ t w₀).loc.Lin (fun j => ⟨Sum.inr (iJ j).1, (iJ j).2⟩)
      (fun q => ⟨Sum.inr (iQ q).1, (iQ q).2⟩) Slf.idf id :=
  lin_loc (vecD (Hd.foldD Sb sl Z A₀)) (closeSel Hd Sb sl Z A₀ cs l iJ iQ t w₀) iJ iQ hC
    (fun _ _ => rfl) fun _ _ => rfl

/-- What the caller claims behind the positions, as rows. -/
theorem after_sel (hC : Sh.Cf.Laws)
    (x : ((closeSel Hd Sb sl Z A₀ cs l iJ iQ t w₀).loc.Xc ×
      (closeSel Hd Sb sl Z A₀ cs l iJ iQ t w₀).loc.hd.Smp) ×
      (closeSel Hd Sb sl Z A₀ cs l iJ iQ t w₀).loc.Lc)
    (m : (closeSel Hd Sb sl Z A₀ cs l iJ iQ t w₀).loc.S.Msg) :
    (closeSel Hd Sb sl Z A₀ cs l iJ iQ t w₀).loc.After x m ↔
      Slf.All (fun _ => Slf.idf)
        ((closeSel Hd Sb sl Z A₀ cs l iJ iQ t w₀).loc.rowsOf (fun j => ⟨Sum.inr (iJ j).1, (iJ j).2⟩)
          (fun q => ⟨Sum.inr (iQ q).1, (iQ q).2⟩) Slf.idf id x)
        ((closeSel Hd Sb sl Z A₀ cs l iJ iQ t w₀).loc.S.ents m) :=
  ldLoc_after_rows GE _ _ _ _ _ _ _ (sel_lin Hd Sb sl Z A₀ cs l iJ iQ t w₀ hC) x m

end Johnson.Top.H

#print axioms Johnson.Top.H.switchSel_loc
#print axioms Johnson.Top.H.switchSel_ok
#print axioms Johnson.Top.H.sel_lin
#print axioms Johnson.Top.H.after_sel
