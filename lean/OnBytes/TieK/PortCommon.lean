-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TieK/PortCommon.lean: the clause of `K.PortYesAt` on the proof file, with every value named
as what the program's functions make of the files.

K.PortYesAt F id table further (OnBytes/K/Top.lean) speaks through a record C that the stages of a
call share. Of C it says that commonOfCall has returned it and that its chains are the plan's. The
clause on the proof file reads C's public part and C's links as built. This file puts the plan's own
in their place: p is what Model.Verify.planned makes of the three public files, and C no longer
occurs.

Main theorem: port_common.
It claims nothing on soundness. The program does not import this file.

-/
import OnBytes.K.Top
import OnBytes.TieK.Built

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.TieK

/-- **The clause on the proof file, at the plan.** so: the request's and the reply's words as read;
cov: the covered positions; item: the statement's item "request"; links: the links made for the
request. Each stands with the equation that makes it from the files. The request file's own bytes
stand beside the item in the check. The last clause: the plan's
links as built are what builtOf makes of the plan's public part and chains. -/
theorem port_common {F : K.Files} {id : String} {table further : Params.TableName}
    (h : K.PortYesAt F id table further) :
    ∃ p so cov item links,
      Model.Verify.planned F.pol F.KL (some F.lay) = .ok p ∧
      Model.Head.stFromCall (Model.Verify.words32 F.request) (Model.Verify.words32 F.y) p.X.T =
        .ok so ∧
      Model.Head.coveredOf so p.X.T p.X.P.h.V = .ok cov ∧
      Proof.requestItem F.pol F.KL F.request = some item ∧
      Model.Verify.linksOf p.X cov = .ok links ∧
      Proof.check p.chains.proof further F.entry item F.request (Model.ofNat so.y)
        (Model.Stages.runLinksH (p.built.links.zipWith (fun b l => { b with run := l.run }) links)
          p.chains.proof.first p.X.layers.wsLay) F.proof = .accepted ∧
      Model.Verify.builtOf p.X p.chains = .ok p.built := by
  obtain ⟨r, p, C, e1, e2, e3, -, -, -, -, -, -, -, hp, hcc, -, -, -,
    ⟨so, cov, item, links, h1, h2, h3, h4, hc⟩, -⟩ := h
  obtain ⟨p', hp', x1, -, x3⟩ := commonOfCall_same hcc
  rw [e1, e2, e3, hp] at hp'
  have ep : p = p' := Except.ok.inj hp'
  subst ep
  rw [x1] at h1 h2 h4 hc
  rw [x3] at hc
  exact ⟨p, so, cov, item, links, hp, h1, h2, h3, h4, hc, planned_built hp⟩

end OnBytes.TieK
