-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/TieVC.lean: the shape of OnBytes/K/TopVC.lean filled with the library's own compiled
verifier with records. This is a pattern; it is not the verifier at which the tie is to be stated.

"The program" is the Lean program `verify-on-bytes` (OnBytes/Main.lean). "The programs" are the
prover and the verifiers that ship. "The tie" is the step from the program's exit code 0 to the yes
of the verifier of which the soundness theorem speaks. OnBytes/K/Top.lean states it at a served
statement, under named hypotheses, and with that verifier left abstract. "The front" is an argument
system in the sense of VerifiableInference/Statements.lean (`ArgumentSystem`); the soundness theorem
speaks of its verifier. The five answers, the typed strings (Test's, Link's and the session's) and
the served statements are explained in the heads of OnBytes/K/Top.lean and OnBytes/K/TopVC.lean.
"The ID's own written code" is the byte string that the programs hash to get the commitment ID.

At this verifier three of the five named hypotheses (`seed0`, `seed1` and `session`) are likely
false as they are spelt, so `Holes5` at `shapeVC` is no hypothesis to build on. The reasons are
these. The programs draw both tables' seeds by one function without a role, by two nested hashes on
the table's name; `VC` asks one query at the root under two different tags. The programs hash the
stored copy's number in the statement of the proof's first chain; the first query of `vBC` has no
place for it. The tie has to be stated at a verifier of the same form as `VC` that is spelt as the
programs hash. This file shows how a verifier's five parts fill the shape, and that its run is their
conjunction (`VC_det`); no file states the tie at that other verifier.

OnBytes/K/TopVC.lean leaves the compiled verifier with records abstract, in its own form. Here its
parameters are filled with the library's terms: `Compile.Batch.Cms.VC` (Johnson/RecCompile/Cms.lean)
and its five parts `seedIs` (twice), `vTC`, `vLC` and `vBC`, each run (`.det`) at typed oracle
functions `g`. What stays a parameter: the object with records `L`, its wires `W` and `S` and the
parameters `p`, all of which come from a protocol's description; `g`, which is to be what the
description's coding of the typed oracles reads out of Lean's BLAKE2b; which statements are served;
and the two plain readings (a table as a record; request and reply as an instance).

Main definitions. `shapeVC`: the shape made of the library's five terms. `keyVC`: the key of `VC`
with one further root.

Main theorems.
- `VC_det`: the run of `VC`, at a key with one further root and the proof that names it, is the
  conjunction of the five runs.
- `exit_VC`: the exit code 0 (`YES` or `WITHIN LIMITS`) gives, at a served statement: the two tables
  that the program hands on from file to file, with `IdIs` of the first; their records; the
  instance; the three typed strings, which the fixed reading of the files gives; and that `VC`, at
  the key made of the first root, its record, Test's string and the one link, at the instance and
  the proof, run at `g`, says yes. This holds under the five named hypotheses of
  OnBytes/K/TopVC.lean at this shape.

On the ID. `VC` itself tests no ID. `IdIs x t` (OnBytes/K/TopVC.lean) says that the ID in the user's
options is, in hexadecimal, the commitment ID of the table `t` under the planner's table shape and
the public files' digest; this is the program's own test of the ID. It is proved of the first table.
"One ID, one table" is no property that can be asked as a hypothesis: it is false by counting
(tables of any length, an ID of 32 bytes). That the ID fixes a table can be said only inside the
game of the front's soundness (index binding), with a term for collisions, and for a front whose
commitment is the hash of the ID's own written code: see Johnson/Top/TieFront.lean.

What is not claimed. What the heads of OnBytes/K/Top.lean and OnBytes/K/TopVC.lean do not claim is
not claimed here. A named hypothesis may be false, and not only unproved. The one further root of
the key comes from the entry file, whose number the proof file names: it is the prover's choice. No
`L`, `W`, `S`, `p` or `g` is given here. The verifier of the final description may be one of the
same form as `VC` over other underlying definitions; this file then serves with that verifier's
terms. For proofs only; the program does not import this file.

-/
import OnBytes.K.TopVC
import Johnson.RecCompile.Cms

set_option autoImplicit false

noncomputable section

namespace OnBytes.K

open OnBytes.Shell (Steps opsIO World Event wholeReads kindOf Asked)
open Iop Rom Compile Compile.Batch Compile.Batch.Cms
open _root_.Run (bytesToDig)

variable {I X : Type} (L : HolographicProtocol I X) (W : QueryLayout 256 L.carrierC) (S : OutOfDomainSampleQueryLayout 256 W.K L) (p : Params)
  (g : Fam (spec 256 W.K L.carrierC)) (Served : UserStm → Prop)
  (recOf : UserStm → OnBytes.Params.TableName → Option L.Rec) (insOf : UserStm → Option X)

/-- The shape made of the library's five terms. -/
def shapeVC : Shape where
  Served := Served
  Rec := fun _ => L.Rec
  Ins := fun _ => X
  PiT := fun _ => OneProtocolProof 256 (BatchInteractiveOracleProof.ofProto L.offline)
  PiL := fun _ => OneProtocolProof 256 (BatchInteractiveOracleProof.ofProto L.link)
  PiB := fun _ => OneProtocolProof 256 L.onlineBatch
  recOf := recOf
  insOf := insOf
  seed0 := fun _ cm r => (seedIs W S S.t0 cm r.1).det g
  seed1 := fun _ cm r => (seedIs W S S.t1 cm r.1).det g
  vT := fun _ cm r π => (vTC W p cm r π).det g
  vL := fun _ cm cm' r r' π => (vLC W p cm cm' r r' π).det g
  vB := fun _ cm i r π => (vBC W S p cm i r π).det g

/-- The key of `VC` with one further root. -/
def keyVC (cm : Dig 256) (r : L.Rec) (πT : OneProtocolProof 256 (BatchInteractiveOracleProof.ofProto L.offline)) (cmj : Dig 256)
    (rj : L.Rec) (πL : OneProtocolProof 256 (BatchInteractiveOracleProof.ofProto L.link)) : FullKey 256 L :=
  ⟨cm, r, some πT, [(cmj, rj, some πL)]⟩

/-- The run of `VC` is the conjunction of the five runs. -/
theorem VC_det (cm : Dig 256) (r : L.Rec) (πT : OneProtocolProof 256 (BatchInteractiveOracleProof.ofProto L.offline))
    (cmj : Dig 256) (rj : L.Rec) (πL : OneProtocolProof 256 (BatchInteractiveOracleProof.ofProto L.link)) (x : X)
    (πB : OneProtocolProof 256 L.onlineBatch) :
    (VC W S p (keyVC L cm r πT cmj rj πL) x ⟨0, some πB⟩).det g =
      ((seedIs W S S.t0 cm r.1).det g && (seedIs W S S.t1 cmj rj.1).det g &&
        (vTC W p cm r πT).det g && (vLC W p cm cmj r rj πL).det g &&
        (vBC W S p cmj x rj πB).det g) := by
  show ((seedIs W S S.t0 cm r.1).bind fun s0 =>
      (seedIs W S S.t1 cmj rj.1).bind fun sj =>
      (vTC W p cm r πT).bind fun a =>
      (vLC W p cm cmj r rj πL).bind fun b =>
      (vBC W S p cmj x rj πB).bind fun c =>
      OComp.pure (s0 && sj && a && b && c)).det g = _
  simp only [OComp.det_bind]
  rfl

/-- The top statement at the library's compiled verifier with records: under `Holes5` at `shapeVC`,
the exit code 0 (`YES` or `WITHIN LIMITS`) gives, at a served statement, that `VC`, run at `g`, says
yes at the key, the instance and the proof made of the two tables' roots, their records (`recOf`),
the instance (`insOf`) and the three typed strings that the fixed reading gives. The hypothesis `H`
is likely false at this shape (see the head), so this theorem is a pattern and nothing to build on.
-/
theorem exit_VC (R : Reading5 (shapeVC L W S p g Served recOf insOf))
    (H : Holes5 (shapeVC L W S p g Served recOf insOf) R) {args : List String} {s s' : World}
    (h : Shell.Run (_root_.main args) s 0 s') :
    ∃ (config ivk request y proof : String) (a : Asked) (F : Files) (t : List Event) (id : String)
      (pre post : List String),
      args = "verify" :: config :: ivk :: request :: y :: proof ::
        (pre ++ "-id" :: id :: post) ∧
      kindOf args = .whole config ivk request y proof a ∧
      Steps opsIO (wholeReads config ivk request y proof F.entry (.bytes F.pol) (.bytes F.KL)
        (.bytes F.lay) (.bytes F.key) (.bytes F.request) (.bytes F.y) (.bytes F.proof)
        (.bytes F.ent) ++ t) s s' ∧
      a.options.id = some id ∧ a.options.bits = 128 ∧
      (Served (stmOf F a.options) →
        ∃ (table further : OnBytes.Params.TableName) (r rj : L.Rec) (i : X)
          (πT : OneProtocolProof 256 (BatchInteractiveOracleProof.ofProto L.offline)) (πL : OneProtocolProof 256 (BatchInteractiveOracleProof.ofProto L.link))
          (πB : OneProtocolProof 256 L.onlineBatch),
          IdIs (stmOf F a.options) table ∧
          recOf (stmOf F a.options) table = some r ∧ recOf (stmOf F a.options) further = some rj ∧
          insOf (stmOf F a.options) = some i ∧
          R.key (stmOf F a.options) F.key = some (table, πT) ∧
          R.ent (stmOf F a.options) F.key F.ent = some (further, πL) ∧
          R.prf (stmOf F a.options) F.ent F.proof F.entry = some πB ∧
          (VC W S p (keyVC L (bytesToDig table.root) r πT (bytesToDig further.root) rj πL) i
            ⟨0, some πB⟩).det g = true) := by
  obtain ⟨config, ivk, request, y, proof, a, F, t, id, pre, post, e, h1, h2, hi, hb, hs⟩ :=
    exit_five (shapeVC L W S p g Served recOf insOf) R H h
  refine ⟨config, ivk, request, y, proof, a, F, t, id, pre, post, e, h1, h2, hi, hb, fun hS => ?_⟩
  obtain ⟨table, further, r, rj, i, πT, πL, πB, hid, hr, hrj, hx, hk, he, hq, s0, s1, vt, vl, vb⟩ :=
    hs hS
  refine ⟨table, further, r, rj, i, πT, πL, πB, hid, hr, hrj, hx, hk, he, hq, ?_⟩
  rw [VC_det]
  have s0 : (seedIs W S S.t0 (bytesToDig table.root) r.1).det g = true := s0
  have s1 : (seedIs W S S.t1 (bytesToDig further.root) rj.1).det g = true := s1
  have vt : (vTC W p (bytesToDig table.root) r πT).det g = true := vt
  have vl : (vLC W p (bytesToDig table.root) (bytesToDig further.root) r rj πL).det g = true := vl
  have vb : (vBC W S p (bytesToDig further.root) i rj πB).det g = true := vb
  rw [s0, s1, vt, vl, vb]
  rfl

end OnBytes.K

#print axioms OnBytes.K.VC_det
#print axioms OnBytes.K.exit_VC
