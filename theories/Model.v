(******************************************************************************)
(* Copyright (c) 2020 Steven Keuchel, Dominique Devriese, Sander Huyghebaert  *)
(* All rights reserved.                                                       *)
(*                                                                            *)
(* Redistribution and use in source and binary forms, with or without         *)
(* modification, are permitted provided that the following conditions are     *)
(* met:                                                                       *)
(*                                                                            *)
(* 1. Redistributions of source code must retain the above copyright notice,  *)
(*    this list of conditions and the following disclaimer.                   *)
(*                                                                            *)
(* 2. Redistributions in binary form must reproduce the above copyright       *)
(*    notice, this list of conditions and the following disclaimer in the     *)
(*    documentation and/or other materials provided with the distribution.    *)
(*                                                                            *)
(* THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS        *)
(* "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED  *)
(* TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR *)
(* PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR          *)
(* CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,      *)
(* EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,        *)
(* PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR         *)
(* PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF     *)
(* LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING       *)
(* NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS         *)
(* SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.               *)
(******************************************************************************)

From Coq Require Import
     Init.Nat
     Program.Tactics
     Strings.String
     ZArith.ZArith
     ZArith.Znat
     micromega.Lia.

From Equations Require Import
     Equations.

From Katamaran Require Import
     Environment
     Iris.Model
     Sep.Hoare
     Sep.Logic
     Specification
     Symbolic.Mutator
     Semantics.

From MinimalCaps Require Import
     Machine Contracts.

From iris.base_logic Require lib.gen_heap lib.iprop.
From iris.base_logic Require Export invariants.
From iris.bi Require interface big_op.
From iris.algebra Require dfrac.
From iris.program_logic Require Import weakestpre adequacy.
From iris.proofmode Require Import string_ident tactics.
From stdpp Require namespaces fin_maps.

Set Implicit Arguments.

Module gh := iris.base_logic.lib.gen_heap.

Module MinCapsSemantics <: Semantics MinCapsBase MinCapsProgram :=
  MakeSemantics MinCapsBase MinCapsProgram.

Ltac destruct_syminstance ?? :=
  repeat
    match type of ?? with
    | Env _ (ctx.snoc _ (MkB ?s _)) =>
        let id := string_to_ident s in
        let fr := fresh id in
        destruct (env.snocView ??) as [?? fr];
        destruct_syminstance ??
    | Env _ ctx.nil => destruct (env.nilView ??)
    | _ => idtac
    end.

Ltac destruct_syminstances :=
  repeat
    match goal with
    | ?? : Env _ (ctx.snoc _ _) |- _ => destruct_syminstance ??
    | ?? : Env _ ctx.nil        |- _ => destruct_syminstance ??
    end.

Module MinCapsModel.

  Import MinCapsBase.
  Import MinCapsSignature.
  Import MinCapsProgram.
  Import MinCapsSpecification.

  Module MinCapsIrisParams <: IrisParameters MinCapsBase MinCapsProgram MinCapsSignature MinCapsSemantics.

  Include IrisPrelims MinCapsBase MinCapsProgram MinCapsSignature MinCapsSemantics.

    Variable maxAddr : nat.

    Section WithIrisNotations.

    Import iris.bi.interface.
    Import iris.bi.big_op.
    Import iris.base_logic.lib.iprop.
    Import iris.base_logic.lib.gen_heap.

    Definition MemVal : Set := Z + Capability.

    Class mcMemGS ?? := McMemGS {
                          (* ghost variable for tracking state of registers *)
                          mc_ghG :> gh.gen_heapGS Z MemVal ??;
                          mc_invNs : namespace
                        }.

    Definition memGpreS : gFunctors -> Set := fun ?? => gh.gen_heapGpreS Z MemVal ??.
    Definition memGS : gFunctors -> Set := mcMemGS.
    Definition mem?? : gFunctors := gh.gen_heap?? Z MemVal.

    Definition mem??_GpreS : forall {??}, subG mem?? ?? -> memGpreS ?? :=
      fun {??} => gh.subG_gen_heapGpreS (?? := ??) (L := Z) (V := MemVal).

    Definition mem_inv : forall {??}, memGS ?? -> Memory -> iProp ?? :=
      fun {??} hG ?? =>
        (??? memmap, gen_heap_interp (hG := mc_ghG (mcMemGS := hG)) memmap ???
                                ??? map_Forall (fun a v => ?? a = v) memmap ???
        )%I.

    Definition liveAddrs : list Addr := seqZ 0 maxAddr.
    Definition initMemMap ?? := (list_to_map (map (fun a => (a , ?? a)) liveAddrs) : gmap Addr MemVal).

    Lemma initMemMap_works ?? : map_Forall (?? (a : Addr) (v : MemVal), ?? a = v) (initMemMap ??).
    Proof.
      unfold initMemMap.
      rewrite map_Forall_to_list.
      rewrite Forall_forall.
      intros (a , v).
      rewrite elem_of_map_to_list.
      intros el.
      apply elem_of_list_to_map_2 in el.
      apply elem_of_list_In in el.
      apply in_map_iff in el.
      by destruct el as (a' & <- & _).
    Qed.

    Definition mem_res : forall {??}, memGS ?? -> Memory -> iProp ?? :=
      fun {??} hG ?? =>
        ([??? map] l???v ??? initMemMap ??, mapsto (hG := mc_ghG (mcMemGS := hG)) l (DfracOwn 1) v) %I.

    Lemma mem_inv_init : forall ?? (?? : Memory), memGpreS ?? ->
      ??? |==> ??? mG : memGS ??, (mem_inv mG ?? ??? mem_res mG ??)%I.
    Proof.
      iIntros (?? ?? gHP).

      iMod (gen_heap_init (gen_heapGpreS0 := gHP) (L := Addr) (V := MemVal) empty) as (gH) "[inv _]".
      pose (memmap := initMemMap ??).
      iMod (gen_heap_alloc_big empty memmap (map_disjoint_empty_r memmap) with "inv") as "(inv & res & _)".
      iModIntro.

      rewrite (right_id empty union memmap).

      iExists (McMemGS gH (nroot .@ "addr_inv")).
      iFrame.
      iExists memmap.
      iFrame.
      iPureIntro.
      apply initMemMap_works.
    Qed.

    Definition MinCaps_ptsreg `{sailRegGS ??} (reg : RegName) (v : Z + Capability) : iProp ?? :=
      match reg with
      | R0 => reg_pointsTo reg0 v
      | R1 => reg_pointsTo reg1 v
      | R2 => reg_pointsTo reg2 v
      | R3 => reg_pointsTo reg3 v
      end.

    Lemma MinCaps_ptsreg_regtag_to_reg `{sailRegGS ??} (reg : RegName) (v : Z + Capability) :
      MinCaps_ptsreg reg v = reg_pointsTo (regtag_to_reg reg) v.
    Proof.
      by destruct reg.
    Qed.

    Definition region_addrs (b e : Addr) : list Addr :=
      filter (fun a => and (b ??? a)%Z (a ??? e)%Z) liveAddrs.

    Lemma element_of_region_addrs (a b e : Addr) :
      b ??? liveAddrs ??? e ??? liveAddrs ???
      (b <= a)%Z /\ (a <= e)%Z ->
      a ??? region_addrs b e.
    Proof.
      intros Hb He [Hba Hae].
      apply elem_of_list_filter.
      repeat (split; try assumption).
      apply elem_of_seqZ in Hb.
      apply elem_of_seqZ in He.
      apply elem_of_seqZ.
      lia.
    Qed.

    Context {?? : gFunctors}.
    Notation D := ((leibnizO MemVal) -n> iPropO ??). (* TODO: try -d>, drop leibnizO, might not need ??ne *)
    Implicit Type w : (leibnizO MemVal).

    (* Copied from github.com/logsem/cerise *)
    (* TODO: include copyright notice =) *)
    Ltac auto_equiv :=
      (* Deal with "pointwise_relation" *)
      repeat lazymatch goal with
             | |- pointwise_relation _ _ _ _ => intros ?
             end;
      (* Normalize away equalities. *)
      repeat match goal with
             | H : _ ???{_}??? _ |-  _ => apply (discrete_iff _ _) in H
             | H : _ ??? _ |-  _ => apply leibniz_equiv in H
             | _ => progress simplify_eq
             end;
      (* repeatedly apply congruence lemmas and use the equalities in the hypotheses. *)
      try (f_equiv; fast_done || auto_equiv).

    Ltac solve_proper ::= (repeat intros ?; simpl; auto_equiv).

    Program Definition MinCaps_ref_inv `{sailRegGS ??} `{invGS ??} {mG : memGS ??} (a : Addr) : D -n> iPropO ?? :=
      ??ne P, (??? w, mapsto (hG := mc_ghG (mcMemGS := mG)) a (DfracOwn 1) w ??? P w)%I.
    Solve All Obligations with solve_proper.

    Program Definition MinCaps_csafe `{sailRegGS ??} `{invGS ??} {mG : memGS ??} (safe : D) : D :=
      ??ne w,
        (match w with
        | inr (MkCap O b e a) => True%I
        | inr (MkCap R b e a) =>
          (??? (b <= e)%Z ??? ???
            ??? b ??? liveAddrs /\ e ??? liveAddrs ??? ???
                                [??? list] a ??? (region_addrs b e), inv (mc_invNs (mcMemGS := mG) .@ a) (MinCaps_ref_inv (mG := mG) a safe))
          ???
          ??? (e < b)%Z ???
        | inr (MkCap RW b e a) =>
          (??? (b <= e)%Z ??? ???
            ??? b ??? liveAddrs /\ e ??? liveAddrs ??? ???
                                [??? list] a ??? (region_addrs b e), inv (mc_invNs (mcMemGS := mG) .@ a) (MinCaps_ref_inv (mG := mG) a safe))
          ???
          ??? (e < b)%Z ???
        | inl _ => False
        end)%I.

    Program Definition MinCaps_safe1 `{sailRegGS ??} `{invGS ??} {mG : memGS ??} (safe : D) : D :=
      ??ne w,
        (match w with
        | inl z => True
        | inr c => MinCaps_csafe (mG := mG) safe w
        end)%I.

    Global Instance MinCaps_csafe_contractive `{sailRegGS ??} `{invGS ??} {mG : memGS ??} :
      Contractive (MinCaps_csafe (mG := mG)).
    Proof.
      intros n x y Hdist w.
      unfold MinCaps_csafe.
      destruct w; first by intuition.
      destruct c.
      destruct cap_permission; first auto; solve_proper_prepare; solve_contractive.
    Qed.

    Global Instance MinCaps_safe1_contractive `{sailRegGS ??} `{invGS ??} {mG : memGS ??} :
      Contractive (MinCaps_safe1 (mG := mG)).
    Proof.
      intros n x y Hdist w.
      unfold MinCaps_safe1.
      destruct w; first by intuition.
      by apply MinCaps_csafe_contractive.
    Qed.

    Lemma fixpoint_MinCaps_safe1_eq `{sailRegGS ??} `{invGS ??} {mG : memGS ??} (w : leibnizO MemVal) :
      fixpoint (MinCaps_safe1 (mG := mG)) w ??? MinCaps_safe1 (mG := mG) (fixpoint (MinCaps_safe1 (mG := mG))) w.
    Proof. exact: (fixpoint_unfold (MinCaps_safe1 (mG := mG)) w). Qed.

    Definition MinCaps_safe `{sailRegGS ??} `{invGS ??} {mG : memGS ??} : D :=
      ??ne w, (fixpoint (MinCaps_safe1 (mG := mG))) w.

    Lemma le_liveAddrs (a b e : Addr) :
      b ??? liveAddrs ??? e ??? liveAddrs ->
      (b <= a)%Z ??? (a <= e)%Z ->
      a ??? liveAddrs.
    Proof.
      intros [Hb He] [Hba Hae].
      apply elem_of_seqZ in Hb.
      apply elem_of_seqZ in He.
      destruct Hb as [H0b Hbm].
      destruct He as [H0e Hem].
      rewrite elem_of_seqZ.
      split; lia.
    Qed.

    Lemma region_addrs_submseteq `{sailRegGS ??} `{invGS ??} {mG : memGS ??} (b' e' b e : Addr) :
      ??? ??? (b <= b')%Z /\ (e' <= e)%Z ??? -???
                               ([??? list] a ??? (region_addrs b e), inv (mc_invNs (mcMemGS := mG) .@ a) (??? w, mapsto (hG := mc_ghG (mcMemGS := mG)) a (DfracOwn 1) w ??? fixpoint (MinCaps_safe1 (mG := mG)) w))%I -???
                               ([??? list] a ??? (region_addrs b' e'), inv (mc_invNs (mcMemGS := mG) .@ a) (??? w, mapsto (hG := mc_ghG (mcMemGS := mG)) a (DfracOwn 1) w ??? fixpoint (MinCaps_safe1 (mG := mG)) w))%I.
    Proof.
      iIntros "[% %] Hregion".
      iApply (big_sepL_submseteq _ (region_addrs b' e') (region_addrs b e)).
      Unshelve. all: eauto with typeclass_instances.
      unfold region_addrs.
      induction liveAddrs.
      - cbn; trivial.
      - cbn.
        destruct (decide ((b' ??? a)%Z ??? (a ??? e')%Z));
          destruct (decide ((b ??? a)%Z ??? (a ??? e)%Z));
          trivial.
        + apply submseteq_skip; trivial.
        + destruct a0 as [Hb' He']; lia.
        + apply submseteq_cons; trivial.
    Qed.

    Lemma safe_sub_range `{sailRegGS ??} `{invGS ??} {mG : memGS ??} (b' e' b e : Addr) :
      forall p a,
      ??? ??? (b <= b')%Z /\ (e' <= e)%Z ??? -???
                               MinCaps_safe (mG := mG)
                               (inr {| cap_permission := p; cap_begin := b; cap_end := e; cap_cursor := a |}) -???
                               MinCaps_safe (mG := mG)
                               (inr {| cap_permission := p; cap_begin := b'; cap_end := e'; cap_cursor := a |}).
    Proof.
      iIntros (p a) "/= [% %] Hsafe".
      do 2 rewrite fixpoint_MinCaps_safe1_eq.
      destruct p; try (by iFrame); simpl; iDestruct "Hsafe" as "/= [Hsafe | %]";
        try (iRight; iPureIntro; lia).
      - iLeft.
        iIntros "%".
        iAssert (??? (b <= e)%Z ???)%I as "-# Htmp".
        { iPureIntro; lia. }
        iAssert (
          ???b ??? liveAddrs ??? e ??? liveAddrs???
                             ??? ([??? list] a0 ??? region_addrs b e, inv (mc_invNs.@a0)
                                                                    (??? w,
                                                                        mapsto a0 (DfracOwn 1) w
                                                                               ??? fixpoint MinCaps_safe1 w))
        )%I with "[Htmp Hsafe]" as "Hsafe".
        { iApply ("Hsafe" with "Htmp"). }
        iDestruct "Hsafe" as "[% H]".
        iSplitR.
        + iPureIntro; split.
          apply (le_liveAddrs H4 (conj H1 (Z.le_trans b' e' e H3 H2))).
          apply (le_liveAddrs H4 (conj (Z.le_trans b b' e' H1 H3) H2)).
        + iApply (region_addrs_submseteq $! (conj H1 H2) with "H").
      - iLeft.
        iIntros "%".
        iAssert (??? (b <= e)%Z ???)%I as "-# Htmp".
        { iPureIntro; lia. }
        iAssert (
          ???b ??? liveAddrs ??? e ??? liveAddrs???
                             ??? ([??? list] a0 ??? region_addrs b e, inv (mc_invNs.@a0)
                                                                    (??? w,
                                                                        mapsto a0 (DfracOwn 1) w
                                                                               ??? fixpoint MinCaps_safe1 w))
        )%I with "[Htmp Hsafe]" as "Hsafe".
        { iApply ("Hsafe" with "Htmp"). }
        iDestruct "Hsafe" as "[% H]".
        iSplitR.
        + iPureIntro; split.
          apply (le_liveAddrs H4 (conj H1 (Z.le_trans b' e' e H3 H2))).
          apply (le_liveAddrs H4 (conj (Z.le_trans b b' e' H1 H3) H2)).
        + iApply (region_addrs_submseteq $! (conj H1 H2) with "H").
    Qed.

    Lemma specialize_range `{sailRegGS ??} `{invGS ??} {mG : memGS ??} (b e addr : Addr) :
      ??? ??? (b <= addr)%Z /\ (addr <= e)%Z ??? -???
        (??? b ??? liveAddrs /\ e ??? liveAddrs ??? ???
          [??? list] a ??? (region_addrs b e), inv (mc_invNs (mcMemGS := mG) .@ a) (??? w, mapsto (hG := mc_ghG (mcMemGS := mG)) a (DfracOwn 1) w ??? fixpoint (MinCaps_safe1 (mG := mG)) w))%I -???
        (inv (mc_invNs (mcMemGS := mG) .@ addr) (??? w, mapsto (hG := mc_ghG (mcMemGS := mG)) addr (DfracOwn 1) w ??? fixpoint (MinCaps_safe1 (mG := mG)) w))%I.
    Proof.
      iIntros "[% %] [[% %] Hrange]".
      iApply (big_sepL_elem_of with "Hrange").
      apply element_of_region_addrs; try assumption.
      split; assumption.
    Qed.

    Definition GPRs : list RegName := finite.enum RegName.

    Definition interp_gprs `{sailRegGS ??} `{invGS ??} `{mG : memGS ??} : iProp ?? :=
      [??? list] r ??? GPRs, (??? w, MinCaps_ptsreg r w ??? MinCaps_safe (mG := mG) w)%I.

    Import env.notations.

    Definition luser_inst `{sailRegGS ??} `{invGS ??} (mG : memGS ??) (p : Predicate) (ts : Env Val (????_Ty p)) : iProp ?? :=
      (match p return Env Val (????_Ty p) -> iProp ?? with
      | ptsreg => fun ts => MinCaps_ptsreg (env.head (env.tail ts)) (env.head ts)
      | ptsto => fun ts => mapsto (hG := mc_ghG (mcMemGS := mG)) (env.head (env.tail ts)) (DfracOwn 1) (env.head ts)
      | safe => fun ts => MinCaps_safe (mG := mG) (env.head ts)
      | dummy => fun ts => True%I
      | gprs => fun ts => interp_gprs (mG := mG)
      end) ts.

    Global Instance MinCaps_safe_Persistent `{sailRegGS ??} `{invGS ??} {mG : memGS ??} (w : leibnizO MemVal) : Persistent (MinCaps_safe (mG := mG) w).
    Proof. destruct w; simpl; rewrite fixpoint_MinCaps_safe1_eq; simpl; first apply _.
           destruct c; destruct cap_permission; apply _. Qed.

    Definition lduplicate_inst `{sailRegGS ??} `{invGS ??} (mG : memGS ??) :
      forall (p : Predicate) (ts : Env Val (????_Ty p)),
        is_duplicable p = true ->
        (luser_inst mG p ts) ??? (luser_inst mG p ts ??? luser_inst mG p ts).
    Proof.
      iIntros (p ts hdup) "H".
      destruct p; inversion hdup;
      iDestruct "H" as "#H";
      auto.
    Qed.

    End WithIrisNotations.
  End MinCapsIrisParams.

  Include IrisInstance MinCapsBase MinCapsSignature MinCapsSemantics MinCapsIrisParams.
  Include ProgramLogicOn MinCapsBase MinCapsSignature MinCapsSpecification.

End MinCapsModel.

Module MinCapsModel2.
  Import MinCapsModel.
  Import MinCapsSignature.
  Import MinCapsSpecification.
  Import MinCapsProgram.
  Import MinCapsIrisParams.
  Module Import MinCapsIrisModel := IrisInstanceWithContracts MinCapsBase MinCapsSignature MinCapsSpecification MinCapsSemantics MinCapsIrisParams MinCapsModel MinCapsModel.

  Section Lemmas.
    Context `{sg : sailGS ??}.

    Lemma gen_dummy_sound :
      ValidLemma lemma_gen_dummy.
    Proof.
      intros ??. destruct_syminstance ??. cbn.
      auto.
    Qed.

    Lemma open_ptsreg_sound :
      ValidLemma lemma_open_ptsreg.
    Proof.
      intros ??. destruct_syminstance ??. cbn.
      destruct reg; auto.
    Qed.

    Lemma close_ptsreg_sound {R} :
      ValidLemma (lemma_close_ptsreg R).
    Proof.
      intros ??. destruct_syminstance ??. cbn.
      rewrite MinCaps_ptsreg_regtag_to_reg; auto.
    Qed.

    Lemma open_gprs_sound :
      ValidLemma lemma_open_gprs.
    Proof.
      intros ??; destruct_syminstance ??; cbn.
      iIntros "[HR0 [HR1 [HR2 [HR3 _]]]]".
      iSplitL "HR0"; try done.
      iSplitL "HR1"; try done.
      iSplitL "HR2"; try done.
    Qed.

    Lemma close_gprs_sound :
      ValidLemma lemma_close_gprs.
    Proof.
      intros ??; destruct_syminstance ??; cbn.
      iIntros "[HR0 [HR1 [HR2 HR3]]]".
      iSplitL "HR0"; try done.
      iSplitL "HR1"; try done.
      iSplitL "HR2"; try done.
      iSplitL "HR3"; try done.
    Qed.

    Lemma int_safe_sound :
      ValidLemma lemma_int_safe.
    Proof.
      intros ??. destruct_syminstance ??. cbn.
      rewrite fixpoint_MinCaps_safe1_eq; auto.
    Qed.

    (* Lemma duplicate_safe_sound : *)
    (*   ValidLemma lemma_duplicate_safe. *)
    (* Proof. *)
    (*   intros ??. destruct_syminstance ??. cbn. *)
    (*   iIntros "#Hsafe". now iSplit. *)
    (* Qed. *)

    Lemma safe_move_cursor_sound :
      ValidLemma lemma_safe_move_cursor.
    Proof.
      intros ??. destruct_syminstance ??. cbn.
      iIntros "#Hsafe".
      iSplit; [done|].
      do 2 rewrite fixpoint_MinCaps_safe1_eq.
      unfold MinCaps_safe1.
      destruct p; auto.
    Qed.

    Lemma safe_sub_perm_sound :
      ValidLemma lemma_safe_sub_perm.
    Proof.
      intros ??. destruct_syminstance ??. cbn.
      iIntros "[#Hsafe %Hp]".
      iSplit; [done|].
      do 2 rewrite fixpoint_MinCaps_safe1_eq.
      destruct p; destruct p'; trivial;
        destruct Hp; discriminate.
    Qed.

    Lemma safe_within_range_sound :
      ValidLemma lemma_safe_within_range.
    Proof.
      intros ??. destruct_syminstance ??. cbn.
      iIntros "[#Hsafe [_ Hp]]".
      iSplit; [done|].
      iDestruct "Hp" as (H) "_".
      unfold is_true in H;
        apply andb_prop in H;
        destruct H as [Hb He];
        apply Zle_is_le_bool in Hb;
        apply Zle_is_le_bool in He.
      iApply (safe_sub_range $! (conj Hb He) with "Hsafe").
    Qed.

  End Lemmas.

  Lemma dI_sound `{sg : sailGS ??} `{invGS} {?? es ??} :
    forall code : Val ty_int,
    evals es ?? = env.snoc env.nil (MkB _ ty_int) code
    ??? ??? semTriple ?? (???is_true true??? ??? emp) (stm_foreign dI es)
          (?? (v : Val ty_instr) (??' : CStore ??),
             (???is_true true??? ??? emp) ??? ?????' = ?????).
  Proof.
    intros code Heq.
    iApply iris_rule_noop; try done.
    intros s' ?? ??' ?? ??' ??' step.
    dependent elimination step.
    rewrite Heq in f1.
    cbn in f1. destruct f1 as [res' e].
    dependent elimination e.
    repeat split; destruct res; eauto.
  Qed.

  Import iris.base_logic.lib.gen_heap.

  Lemma rM_sound `{sg : sailGS ??} `{invGS} {?? es ??} :
    forall a (p : Val ty_perm) (b e : Val ty_addr),
      evals es ?? = env.snoc env.nil (MkB _ ty_addr) a ->
    ??? semTriple ??
        (MinCaps_safe (mG := sailGS_memGS)
           (inr {| cap_permission := p; cap_begin := b; cap_end := e; cap_cursor := a |})
         ??? (???Subperm R p??? ??? emp) ??? ???(b <=? a)%Z && (a <=? e)%Z = true??? ??? emp)
        (stm_foreign rM es)%env
        (?? (v : Z + Capability) (??' : CStore ??),
           (MinCaps_safe (mG := sailGS_memGS) v) ??? ?????' = ?????).
  Proof.
    intros a p b e Heq.
    iIntros "[#Hsafe [[%Hsubp _] [%Hbounds _]]]".
    apply andb_prop in Hbounds as [Hb%Zle_is_le_bool He%Zle_is_le_bool].
    rewrite wp_unfold. cbn.
    destruct p; try discriminate.
    (* TODO: clean this up! *)
    - iAssert (inv (mc_invNs.@a) (??? w, gen_heap.mapsto a (dfrac.DfracOwn 1) w ??? MinCaps_safe w))%I as "Hown".
      { rewrite fixpoint_MinCaps_safe1_eq; simpl.
        iDestruct "Hsafe" as "[Hsafe | %]"; try lia.
        iAssert (??? (b <= e)%Z ???)%I as "-# Htmp".
        { iPureIntro; lia. }
        iAssert (
          ???b ??? liveAddrs ??? e ??? liveAddrs???
                             ??? ([??? list] a0 ??? region_addrs b e,
                                inv (mc_invNs.@a0) (??? w, mapsto a0 (DfracOwn 1) w
                                                        ??? fixpoint MinCaps_safe1 w))
        )%I with "[Htmp Hsafe]" as "Hsafe'".
        { iApply ("Hsafe" with "Htmp"). }
        iApply (specialize_range $! (conj Hb He) with "Hsafe'"). }
      iIntros (??' ns ks1 ks nt) "[Hregs Hmem]".
      iDestruct "Hmem" as (memmap) "[Hmem' %]".
      iInv "Hown" as "Hinv" "Hclose".
      iMod (fupd_mask_subseteq empty) as "Hclose2"; first set_solver.
      iModIntro.
      iSplitR; first by intuition.
      iIntros (e2 ??'' efs) "%".
      dependent elimination H1.
      dependent elimination s.
      rewrite Heq in f1.
      cbn in f1.
      dependent elimination f1.
      do 3 iModIntro.
      iDestruct "Hinv" as (v) "Hav".
      iDestruct "Hav" as "[Hav #Hrec]".
      iAssert (??? memmap !! a = Some v ???)%I with "[Hav Hmem']" as "%".
      { iApply (gen_heap.gen_heap_valid with "Hmem' Hav"). }
      iMod "Hclose2" as "_".
      iAssert (??? (??? v0 : Z + Capability, gen_heap.mapsto a (dfrac.DfracOwn 1) v0 ??? fixpoint MinCaps_safe1 v0))%I with "[Hav Hrec]" as "Hinv".
      { iModIntro. iExists v. iSplitL "Hav"; iAssumption. }
      iMod ("Hclose" with "Hinv") as "_".
      iModIntro.
      cbn.
      iSplitL "Hmem' Hregs".
      iSplitL "Hregs"; first iFrame.
      iExists memmap.
      iSplitL "Hmem'"; first iFrame.
      iPureIntro; assumption.
      iSplitL; trivial.
      iApply wp_value; cbn.
      iSplitL; trivial.
      unfold fun_rM.
      apply map_Forall_lookup_1 with (i := a) (x := v) in H0; auto.
      simpl in H0. subst.
      iAssumption.
    - iAssert (inv (mc_invNs.@a) (??? w, gen_heap.mapsto a (dfrac.DfracOwn 1) w ??? fixpoint (MinCaps_safe1) w))%I as "Hown".
      { rewrite fixpoint_MinCaps_safe1_eq; simpl.
        iDestruct "Hsafe" as "[Hsafe | %]"; try lia.
        iAssert (??? (b <= e)%Z ???)%I as "-# Htmp".
        { iPureIntro; lia. }
        iAssert (
          ???b ??? liveAddrs ??? e ??? liveAddrs???
                             ??? ([??? list] a0 ??? region_addrs b e,
                                inv (mc_invNs.@a0) (??? w, mapsto a0 (DfracOwn 1) w
                                                        ??? fixpoint MinCaps_safe1 w))
        )%I with "[Htmp Hsafe]" as "Hsafe'".
        { iApply ("Hsafe" with "Htmp"). }
        iApply (specialize_range $! (conj Hb He) with "Hsafe'"). }
      iIntros (??' ns ks1 ks nt) "[Hregs Hmem]".
      iDestruct "Hmem" as (memmap) "[Hmem' %]".
      iInv "Hown" as "Hinv" "Hclose".
      iMod (fupd_mask_subseteq empty) as "Hclose2"; first set_solver.
      iModIntro.
      iSplitR; first by intuition.
      iIntros (e2 ??'' efs) "%".
      dependent elimination H1.
      dependent elimination s.
      rewrite Heq in f1.
      cbn in f1.
      dependent elimination f1.
      do 3 iModIntro.
      iDestruct "Hinv" as (v) "Hav".
      iDestruct "Hav" as "[Hav #Hrec]".
      iAssert (??? memmap !! a = Some v ???)%I with "[Hav Hmem']" as "%".
      { iApply (gen_heap.gen_heap_valid with "Hmem' Hav"). }
      iMod "Hclose2" as "_".
      iAssert (??? (??? v0 : Z + Capability, gen_heap.mapsto a (dfrac.DfracOwn 1) v0 ??? fixpoint MinCaps_safe1 v0))%I with "[Hav Hrec]" as "Hinv".
      { iModIntro. iExists v. iSplitL "Hav"; iAssumption. }
      iMod ("Hclose" with "Hinv") as "_".
      iModIntro.
      cbn.
      iSplitL "Hmem' Hregs".
      iSplitL "Hregs"; first iFrame.
      iExists memmap.
      iSplitL "Hmem'"; first iFrame.
      iPureIntro; assumption.
      iSplitL; trivial.
      iApply wp_value; cbn.
      iSplitL; trivial.
      unfold fun_rM.
      apply map_Forall_lookup_1 with (i := a) (x := v) in H0; auto.
      simpl in H0. subst.
      iAssumption.
  Qed.

  Lemma wM_sound `{sg : sailGS ??} `{invGS} {?? es ??} :
    forall a w (p : Val ty_perm) (b e : Val ty_addr),
      evals es ?? = env.snoc (env.snoc env.nil (MkB _ ty_addr) a)
                            (MkB _ ty_memval) w
    ??? ??? semTriple ??
        (MinCaps_safe (mG := sailGS_memGS) w
         ??? MinCaps_safe (mG := sailGS_memGS)
                                          (inr {|
                                               cap_permission := p;
                                               cap_begin := b;
                                               cap_end := e;
                                               cap_cursor := a |})
         ??? (??? Subperm RW p ??? ??? emp)
         ??? ???is_true ((b <=? a)%Z && (a <=? e)%Z)??? ??? emp)
        (stm_foreign wM es)
        (?? (v3 : ()) (??' : CStore ??),
         (???v3 = tt??? ??? emp) ??? ?????' = ?????).
    Proof.
      intros a w p b e Heq.
      iIntros "[#Hwsafe [#Hsafe [[%Hsubp _] [%Hbounds _]]]]".
      apply andb_prop in Hbounds as [Hb%Zle_is_le_bool He%Zle_is_le_bool].
      rewrite wp_unfold. cbn.
      destruct p; try discriminate. clear Hsubp.
      iIntros (??' ns ks1 ks nt) "[Hregs Hmem]".
      iDestruct "Hmem" as (memmap) "[Hmem' %]".
      iAssert (inv (mc_invNs.@a) (??? w, gen_heap.mapsto a (dfrac.DfracOwn 1) w ??? fixpoint (MinCaps_safe1) w))%I as "Hown".
      { do 2 rewrite fixpoint_MinCaps_safe1_eq; simpl.
        iDestruct "Hsafe" as "[Hsafe | %]"; try lia.
        iAssert (??? (b <= e)%Z ???)%I as "-# Htmp".
        { iPureIntro; lia. }
        iAssert (
          ???b ??? liveAddrs ??? e ??? liveAddrs???
                             ??? ([??? list] a0 ??? region_addrs b e,
                                inv (mc_invNs.@a0) (??? w, mapsto a0 (DfracOwn 1) w
                                                        ??? fixpoint MinCaps_safe1 w))
        )%I with "[Htmp Hsafe]" as "Hsafe'".
        { iApply ("Hsafe" with "Htmp"). }
        iApply (specialize_range $! (conj Hb He) with "Hsafe'"). }
      iInv "Hown" as "Hinv" "Hclose".
      iMod (fupd_mask_subseteq empty) as "Hclose2"; first set_solver.
      iModIntro.
      iSplitR; first by intuition.
      iIntros (e2 ??'' efs) "%".
      dependent elimination H1.
      dependent elimination s.
      rewrite Heq in f1.
      cbn in f1.
      dependent elimination f1.
      do 3 iModIntro.
      iDestruct "Hinv" as (v) "Hav".
      iDestruct "Hav" as "[Hav Hrec]".
      iMod (gen_heap.gen_heap_update _ _ _ w with "Hmem' Hav") as "[Hmem' Hav]".
      iMod "Hclose2" as "_".
      iAssert (??? (??? v0 : Z + Capability, gen_heap.mapsto a (dfrac.DfracOwn 1) v0 ??? fixpoint MinCaps_safe1 v0))%I with "[Hav Hrec]" as "Hinv".
      { iModIntro. iExists w. iSplitL "Hav"; iAssumption. }
      iMod ("Hclose" with "Hinv") as "_".
      iModIntro.
      iSplitL; trivial.
      cbn.
      iSplitL "Hregs"; first by iFrame.
      - iExists (<[a:=w]> memmap).
        iSplitL; first by iFrame.
        iPureIntro.
          apply map_Forall_lookup.
          intros i x Hl.
          unfold fun_wM.
          cbn in *.
          destruct (Z.eqb a i) eqn:Heqb.
          + rewrite -> Z.eqb_eq in Heqb.
            subst.
            apply (lookup_insert_rev memmap i); assumption.
          + rewrite -> map_Forall_lookup in H0.
            rewrite -> Z.eqb_neq in Heqb.
            rewrite -> (lookup_insert_ne _ _ _ _ Heqb) in Hl.
            apply H0; assumption.
      - iSplitL; trivial.
        iApply wp_value; cbn; trivial;
          repeat (iSplitL; trivial).
    Qed.

  Lemma foreignSem : ForeignSem.
  Proof.
    intros ?? ?? ?? f es ??.
    destruct f; cbn - [MinCaps_safe MinCaps_csafe];
      intros ??; destruct_syminstance ??;
        eauto using dI_sound, rM_sound, wM_sound.
  Qed.

  Lemma lemSem : LemmaSem.
  Proof.
    intros ?? []; eauto using
      open_ptsreg_sound, close_ptsreg_sound,
      open_gprs_sound, close_gprs_sound, int_safe_sound,
      safe_move_cursor_sound, safe_sub_perm_sound,
      safe_within_range_sound, gen_dummy_sound.
  Qed.

End MinCapsModel2.
