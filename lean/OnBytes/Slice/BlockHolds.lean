-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BlockHolds.lean: the four blocks after the link's fifth round, as statements.

The link is the format's protocol between two stored tables. After its first five rounds come the
batching and the proximity test: folds, code switches and the base case. Each of these blocks is
taken off by a theorem of one form: if the claim before the block has no witness, the prover has
lost (the library's `Doomed`, Iop/Rbr.lean) in the block's rounds and what follows, provided that it
has lost in what follows whenever the claim that the format's own function computes after the block
has no witness. The goal is asked to hold of every transcript in which a test of work fails or the
format's function gives no claim (in the base case: says no). This file writes that form down once
for each kind of block, as a proposition in the stage, the radius, the written rounds and the error
counts. The files on the blocks prove these propositions. The file that joins the blocks assumes
them.

Main definitions: `FoldHolds`, `CsHolds`, `BaseHolds`, `BatHolds`.
Not claimed. No theorem is in this file.
-/
import Fmt.M3Dec
import OnBytes.Slice.Stage

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Run

/-- A fold is taken off, with the error counts εf. -/
def FoldHolds (s : Sg) (e : ℕ) (dE dT : PQ.RD)
    (εf : Err (PQ.uL (ckP .two) (dE :: List.replicate (s.h + s.g) dT))) : Prop :=
  ∀ (t : Shape) (εt : Err t) (G : Fmt.M1.GRow) (col : ℕ → Fmt.M1.Col),
    (∀ w, ¬ s.RIn e (stmIn s G, wordIn s col) w) →
    ∀ bad : Tr (PQ.uL (ckP .two) (dE :: List.replicate (s.h + s.g) dT) ++ t) → Prop,
    (∀ τ b, PQ.passSL (ckP .two) _ (PQ.rhoSL (ckP .two) _ τ) = false → bad (Tr.app τ b)) →
    (∀ (τ : Tr (PQ.uL (ckP .two) (dE :: List.replicate (s.h + s.g) dT))) sigma eps ps rs1 qs g,
      Fmt.M1.nextN 1 1 0 (rsOf _ τ) = some (⟨[sigma], [eps], ps⟩, rs1) →
      Fmt.M1.takeRounds (s.h + s.g) rs1 = some (qs, g, []) →
      (∀ w, ¬ s.RMid e (stmMid s (Fmt.M1.foldStep .two (s.h + s.g) s.h G sigma eps qs g),
        wordMid s col (ptL _ g)) w) →
      Doomed t εt fun b => bad (Tr.app τ b)) →
    Doomed _ (Err.app εf εt) bad

/-- A code switch is taken off, with the error counts εc. -/
def CsHolds (s s' : Sg) (e e' : ℕ) (dS dC : PQ.RD) (εc : Err (PQ.uL (ckP .two) [dS, dC])) : Prop :=
  ∀ (t : Shape) (εt : Err t) (R : Fmt.M1.SRow), R.g.length = s.h + s.g →
    ∀ (col : ℕ → Fmt.M1.Col) (cols : ℕ → Option Fmt.M1.Col),
    (∀ x c, cols x = some c → c = col x) →
    ∀ fW : (wRound dS).Msg → s'.cIn.Word,
    (∀ w, ¬ s.RMid e (stmMid s R, wordMid s col (ptL _ R.g)) w) →
    ∀ bad : Tr (PQ.uL (ckP .two) [dS, dC] ++ t) → Prop,
    (∀ τ b, PQ.passSL (ckP .two) _ (PQ.rhoSL (ckP .two) _ τ) = false → bad (Tr.app τ b)) →
    (∀ (τ : Tr (PQ.uL (ckP .two) [dS, dC])) z beta rs3 alpha theta xs G',
      Fmt.M1.seedOf s'.st.na (rsOf _ τ) = some (z, beta, rs3) →
      Fmt.M1.nextN 1 1 s.t rs3 = some (⟨[alpha], [theta], xs⟩, []) →
      Fmt.M1.csStep .two s.st s'.st R (Fmt.M1.sampleRow .two s'.st.Am s'.st.Az z beta alpha) xs
        theta cols = some G' →
      (∀ w, ¬ s'.RIn e' (stmIn s' G', fW τ.1) w) →
      Doomed t εt fun b => bad (Tr.app τ b)) →
    (∀ (τ : Tr (PQ.uL (ckP .two) [dS, dC])) z beta rs3 alpha theta xs,
      Fmt.M1.seedOf s'.st.na (rsOf _ τ) = some (z, beta, rs3) →
      Fmt.M1.nextN 1 1 s.t rs3 = some (⟨[alpha], [theta], xs⟩, []) →
      Fmt.M1.csStep .two s.st s'.st R (Fmt.M1.sampleRow .two s'.st.Am s'.st.Az z beta alpha) xs
        theta cols = none → ∀ b, bad (Tr.app τ b)) →
    Doomed _ (Err.app εc εt) bad

/-- The base case is taken off, with the error counts εb. -/
def BaseHolds (s : Sg) (e : ℕ) (dL dB : PQ.RD) (εb : Err (PQ.uL (ckP .two) [dL, dB])) : Prop :=
  ∀ (G : Fmt.M1.GRow) (col : ℕ → Fmt.M1.Col) (mk : ℕ → Fmt.M1.E × Fmt.M1.E)
    (last : Tr (PQ.uL (ckP .two) [dL, dB]) →
      ℕ → Option (Fmt.M1.E × Fmt.M1.E × Fmt.M1.E × Fmt.M1.E)),
    (∀ τ x q, last τ x = some q → Fmt.M1.ent (col x).main 0 = q.1 ∧ (mk x).1 = q.2.1 ∧
      Fmt.M1.ent (col x).mask 0 = q.2.2.1 ∧ (mk x).2 = q.2.2.2) →
    (∀ w, ¬ s.RIn e (stmIn s G, wordIn s col) w) →
    ∀ bad : Tr (PQ.uL (ckP .two) [dL, dB]) → Prop,
    (∀ τ, PQ.passSL (ckP .two) _ (PQ.rhoSL (ckP .two) _ τ) = false → bad τ) →
    (∀ (τ : Tr (PQ.uL (ckP .two) [dL, dB])) tauS lam ps rs1 v,
      Fmt.M1.nextN 1 1 0 (rsOf _ τ) = some (⟨[tauS], [lam], ps⟩, rs1) →
      Fmt.M1.nextN (s.C.l + s.Z.l + s.C.r + s.Z.r) 0 s.t rs1 = some (v, []) →
      Fmt.M1.baseOK .two s.C s.Z G.c G.d G.t tauS lam (v.sent.take s.C.l)
        ((v.sent.drop s.C.l).take s.Z.l) ((v.sent.drop (s.C.l + s.Z.l)).take s.C.r)
        (v.sent.drop (s.C.l + s.Z.l + s.C.r)) v.poss (last τ) = false → bad τ) →
    Doomed _ εb bad

/-- The batching is taken off, with the error count εa. -/
def BatHolds (S : Sz) (s : Sg) (e : ℕ) (d1 d2 d3 d4 d5 dA : PQ.RD) (εa : ℕ) : Prop :=
  ∀ (t : Shape) (εt : Err t) (y : S.lk.E0.Str) (V : Fmt.M3.View),
    (∀ (x : S.Pos) (c : List UInt64),
      (Fmt.M3.storedAt V 0 x.val = some c → c = (y.1 x).2) ∧
      (Fmt.M3.storedAt V 1 x.val = some c → c = (y.2 x).2)) →
    ∀ (m1 : (wRound d1).Msg) (c1 : (wRound d1).Chal) (m2 : (wRound d2).Msg)
      (c2 : (wRound d2).Chal) (m3 : (wRound d3).Msg) (c3 : (wRound d3).Chal)
      (m4 : (wRound d4).Msg) (c4 : (wRound d4).Chal) (m5 : (wRound d5).Msg)
      (c5 : (wRound d5).Chal) (col : ℕ → Fmt.M1.Col),
    (∀ x : Fin (2 ^ S.P.C.a),
      (Fmt.M2.groupCol S.P.mems 1 (colW d2 m2.1 x.val)).map (·.col) = some (col x.val)) →
    (∀ w, ¬ S.lk.j4.cf.relR (st4 S d1 d2 d3 d4 d5 y c1 m2 c2 m3 c4 c5) w) →
    ∀ bad : Tr (wRound dA :: t) → Prop,
    (∀ m c τ, GChal.pass (b := dA.entry.work) c = false → bad (m, c, τ)) →
    (∀ (m : (wRound dA).Msg) (c : (wRound dA).Chal) theta R,
      (rvOf dA m c).els = [theta] →
      Fmt.M3.batchLit S.P V (rvOf d1 m1 c1).els ((rvOf d2 m2 c2).els.take (S.P.aR + S.P.aP))
        ((rvOf d2 m2 c2).els.getD (S.P.aR + S.P.aP) Fmt.Fld.zeroE)
        ((rvOf d3 m3 c3).sent.getD 0 Fmt.Fld.zeroE) ((rvOf d3 m3 c3).sent.getD 1 Fmt.Fld.zeroE)
        (rvOf d4 m4 c4).poss (rvOf d5 m5 c5).els theta = some R →
      (∀ w, ¬ s.RIn e (stmIn s R.toG, wordIn s col) w) →
      Doomed t εt fun b => bad (m, c, b)) →
    (∀ (m : (wRound dA).Msg) (c : (wRound dA).Chal) theta,
      (rvOf dA m c).els = [theta] →
      Fmt.M3.batchLit S.P V (rvOf d1 m1 c1).els ((rvOf d2 m2 c2).els.take (S.P.aR + S.P.aP))
        ((rvOf d2 m2 c2).els.getD (S.P.aR + S.P.aP) Fmt.Fld.zeroE)
        ((rvOf d3 m3 c3).sent.getD 0 Fmt.Fld.zeroE) ((rvOf d3 m3 c3).sent.getD 1 Fmt.Fld.zeroE)
        (rvOf d4 m4 c4).poss (rvOf d5 m5 c5).els theta = none → ∀ b, bad (m, c, b)) →
    Doomed (wRound dA :: t) (εa, εt) bad

end OnBytes.Slice
