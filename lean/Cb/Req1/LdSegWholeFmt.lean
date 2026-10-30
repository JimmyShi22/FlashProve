-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdSegWholeFmt.lean: the format of a segment with one group, and of the ghost step.

Statements (Cb.Spec.ldSegWholeFmt_*) and proofs, from the formats move by move
(Cb/Req1/LdSegFormatMoves.lean). Framework only; no place of a text is rendered.
Names and paths: the format of a joint, of a link: `JFmt`, `Link.Fmt` (Cb/Req1/LdReqFormat.lean); of
a move, a list, a segment: `LdMv.Fmt`, `LdProg.Fmt`, `LdSeg.Fmt` (Cb/Req1/LdSegFormat.lean);
"bears": `IOR.Bears` (Ior/Bears.lean); `segOne`: Cb/Req1/LdSegWhole.lean; the ghost step:
`LdStage.ghostMv` (Cb/Req1/LdSegGhost.lean).

Main names:
  `Spec.ldSegWholeFmt_one`: (segOne ..).Fmt from: the body's format; the link `l` (bridge-to-fold)
    has the format up to its joint; `Q.snd.Hyp`; the sender hands on what is read off the further
    witness; and the demands on positions, backwards:
    what follows the segment asks sets within q'; the locations need: their t locations of the open
    word, and these sets at their old places: within the demand after the sending (the demand qc
    before it on the old oracles, at most `Q.tN a` long positions of each new member a);
    qc, under the re-bracketing behind the fold, is within the demand qm at `D.fold.mid`; the link
    `l` bears qm from q.
  `Spec.ldSegWholeFmt_ghost`: the step that copies the core into the further witness has the format,
    for any reader of the old further witness.

Limits: this file says nothing on two groups, and nothing on the last three moves of a request
(Cb/Obj/LdObjectReqEnd.lean). It does not say that the demands can be met together (numbers of
positions against what the encodings bear): an instance's matter.
Terms: lean/GLOSSARY.md.
-/
import Cb.Req1.LdSegWhole
import Cb.Req1.LdSegGhost
import Cb.Req1.LdSegFormatMoves
import Cb.Req1.LdSegRefLkpPreProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR IOR.Chain

namespace Spec

/-- Under the hypotheses below, a segment with one group has the format. -/
def ldSegWholeFmt_one : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (E0 : ExtSpec) (Rc Pw : Type) (a : LdStage E Kc)
      (D : LdCl1 E Kc) (body : LdProg a D.bat.src)
      (hT : body.All fun t => t = .send ∨ t = .sub ∨ t = .step)
      (l : Link Kc D.fold.src.J D.fold.mid) (Q : LdCloseD D.fold) (φ : JFmt Kc E0 Rc Pw a.J)
      (i : IxAt E0 D.E₀) (rc : D.St₀ → Rc) (px : D.Wp → Pw) (px' : Q.Wp' → Pw)
      (q : Finset D.bat.src.Ex.Pos → Prop) (qm : Finset D.fold.mid.E.Pos → Prop)
      (qc : Finset D.fold.tgt.Ex.Pos → Prop) (q' : Finset Q.loc.tgt.Ex.Pos → Prop),
    body.Fmt φ (D.bat.src.fmt i (fun st => rc st.2) px q) →
    l.Fmt (D.fold.src.fmt i (fun st => rc st.2) px q) (D.fold.fmtMid i rc px qm) →
    (∀ U V, (∀ x, x ∈ V ↔ ∃ u ∈ U, x ∈ D.fold.pE.src u) → qc U → qm V) → Q.snd.Hyp →
    (∀ w, px' (Q.Sn.rest w).2 = px w.2.2) →
    (∀ ρ U, q' U → D.fold.tgt.S.qSum Q.N qc Q.tN (Q.loc.link.R.need ρ U)) →
    (segOne D body hT l Q).Fmt φ (Q.loc.tgt.fmt i (fun st => rc st.2) px' q')

/-- The ghost step has the format. -/
def ldSegWholeFmt_ghost : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (E0 : ExtSpec) (Rc Pw : Type) (a : LdStage E Kc)
      (i : IxAt E0 a.E₀) (rc : a.St → Rc) (px : a.Wp → Pw) (q : Finset a.Ex.Pos → Prop),
    a.ghostMv.Fmt (a.fmt i rc px q) (a.ghost.fmt i rc (fun w => px w.1) q)

end Spec

theorem ldSegWholeFmt_one : Spec.ldSegWholeFmt_one := by
  intro E Kc _ _ E0 Rc Pw a D body hT l Q φ i rc px px' q qm qc q' hb hl hqm hs hpx hq'
  refine ⟨D.bat.src.fmt i (fun st => rc st.2) px q,
    D.fold.src.fmt i (fun st => rc st.2) px q,
    D.fold.tgt.fmt (i.inr D.Cf.ext) (fun st => rc st.2) (fun w => px w.2) qc,
    Q.snd.tgt.fmt (i.inr D.Cf.ext) (fun st => rc st.2) px' (D.fold.tgt.S.qSum Q.N qc Q.tN),
    hb, ?_, ?_, ?_, ?_⟩
  · show D.batP.Fmt _ _
    unfold LdCl1.batP
    refine (LdProg.fmt_snoc _ _ _ _).2
      ⟨D.bat.tgt.fmt i (fun st => rc st.2) px q,
        (LdProg.fmt_snoc _ _ _ _).2 ⟨_, (LdProg.fmt_nil _ _ _).2 rfl, ?_⟩,
        ?_⟩
    · exact (fmt_one _ _ _).2 (ldFmt_bat E Kc E0 Rc Pw D.bat i rc px q)
    · unfold LdCl1.step
      exact ldStepF_fmt D.S _ _ _ i _ _ px q (fun _ => rfl)
  · show (Q.foldP l).Fmt _ _
    unfold LdCloseD.foldP
    exact (LdProg.fmt_snoc _ _ _ _).2
      ⟨_, (LdProg.fmt_nil _ _ _).2 rfl,
        (fmt_one _ _ _).2 (ldFmt_fold E Kc E0 Rc Pw D.fold l i rc px q qm qc hl hqm)⟩
  · exact ldFmt_send E Kc E0 Rc Pw D.fold.tgt Q.snd (i.inr D.Cf.ext) (fun st => rc st.2)
      (fun w => px w.2) px' qc hs hpx
  · show Q.locP.Fmt _ _
    unfold LdCloseD.locP
    exact (LdProg.fmt_snoc _ _ _ _).2
      ⟨_, (LdProg.fmt_nil _ _ _).2 rfl,
        (fmt_one _ _ _).2 (ldFmt_loc E Kc E0 Rc Pw Q.loc i rc px' _ q' hq')⟩

theorem ldSegWholeFmt_ghost : Spec.ldSegWholeFmt_ghost := by
  intro E Kc _ _ E0 Rc Pw a i rc px q
  unfold LdStage.ghostMv
  refine ldFmt_step E Kc E0 Rc Pw _ _ _ _ _ _ _ _
    (ExtMap.Moves.pair_left (ExtMap.Moves.comp (ExtMap.Moves.id i) (ExtMap.Moves.fst i a.S.ext))
      (ExtMap.Avoids.snd i a.S.ext))
    ?_ (fun _ => rfl) ?_
  · intro x x' e
    obtain rfl := Option.some.inj e
    rfl
  · intro U V hV hU
    have e : V = U :=
      Finset.ext fun x =>
        (hV x).trans ⟨fun ⟨u, hu, hx⟩ => ((sideG_id_mem a.S a.E₀ u x).1 hx) ▸ hu,
          fun hx => ⟨x, hx, (sideG_id_mem a.S a.E₀ x x).2 rfl⟩⟩
    rw [e]
    exact hU

end Cb
