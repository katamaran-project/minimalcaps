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
From iris.proofmode Require Import tactics.
From iris_string_ident Require Import ltac2_string_ident.
From stdpp Require namespaces fin_maps.

Set Implicit Arguments.

Module gh := iris.base_logic.lib.gen_heap.

Module MinCapsSemantics <: Semantics MinCapsBase MinCapsProgram :=
  MakeSemantics MinCapsBase MinCapsProgram.

Module MinCapsModel.

  Import MinCapsBase.
  Import MinCapsProgram.
  Import MinCapsSpecification.

  Include ProgramLogicOn MinCapsBase MinCapsSpecification.
  Include Iris MinCapsBase MinCapsSpecification MinCapsSemantics.

  Ltac destruct_syminstance ι :=
    repeat
      match type of ι with
      | Env _ (ctx.snoc _ (MkB ?s _)) =>
        let id := string_to_ident s in
        let fr := fresh id in
        destruct (env.snocView ι) as [ι fr];
        destruct_syminstance ι
      | Env _ ctx.nil => destruct (env.nilView ι)
      | _ => idtac
      end.

  Ltac destruct_syminstances :=
    repeat
      match goal with
      | ι : Env _ (ctx.snoc _ _) |- _ => destruct_syminstance ι
      | ι : Env _ ctx.nil        |- _ => destruct_syminstance ι
      end.

  Module MinCapsIrisHeapKit <: IrisHeapKit.

    Variable maxAddr : nat.

    Section WithIrisNotations.

    Import iris.bi.interface.
    Import iris.bi.big_op.
    Import iris.base_logic.lib.iprop.
    Import iris.base_logic.lib.gen_heap.

    Definition MemVal : Set := Z + Capability.

    Class mcMemG Σ := McMemG {
                          (* ghost variable for tracking state of registers *)
                          mc_ghG :> gh.gen_heapG Z MemVal Σ;
                          mc_invNs : namespace
                        }.

    Definition memPreG : gFunctors -> Set := fun Σ => gh.gen_heapPreG Z MemVal Σ.
    Definition memG : gFunctors -> Set := mcMemG.
    Definition memΣ : gFunctors := gh.gen_heapΣ Z MemVal.

    Definition memΣ_PreG : forall {Σ}, subG memΣ Σ -> memPreG Σ := fun {Σ} => gh.subG_gen_heapPreG (Σ := Σ) (L := Z) (V := MemVal).

    Definition mem_inv : forall {Σ}, memG Σ -> Memory -> iProp Σ :=
      fun {Σ} hG μ =>
        (∃ memmap, gen_heap_interp (hG := mc_ghG (mcMemG := hG)) memmap ∗
                                ⌜ map_Forall (fun a v => μ a = v) memmap ⌝
        )%I.

    Definition liveAddrs : list Addr := seqZ 0 maxAddr.
    Definition initMemMap μ := (list_to_map (map (fun a => (a , μ a)) liveAddrs) : gmap Addr MemVal).

    Lemma initMemMap_works μ : map_Forall (λ (a : Addr) (v : MemVal), μ a = v) (initMemMap μ).
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

    Definition mem_res : forall {Σ}, memG Σ -> Memory -> iProp Σ :=
      fun {Σ} hG μ =>
        ([∗ map] l↦v ∈ initMemMap μ, mapsto (hG := mc_ghG (mcMemG := hG)) l (DfracOwn 1) v) %I.

    Lemma mem_inv_init : forall Σ (μ : Memory), memPreG Σ ->
        ⊢ |==> ∃ memG : memG Σ, (mem_inv memG μ ∗ mem_res memG μ)%I.
    Proof.
      iIntros (Σ μ gHP).

      iMod (gen_heap_init (gen_heapPreG0 := gHP) (L := Addr) (V := MemVal) empty) as (gH) "[inv _]".
      pose (memmap := initMemMap μ).
      iMod (gen_heap_alloc_big empty memmap (map_disjoint_empty_r memmap) with "inv") as "(inv & res & _)".
      iModIntro.

      rewrite (right_id empty union memmap).

      iExists (McMemG gH (nroot .@ "addr_inv")).
      iFrame.
      iExists memmap.
      iFrame.
      iPureIntro.
      apply initMemMap_works.
    Qed.

    Definition MinCaps_ptsreg `{sailRegG Σ} (reg : RegName) (v : Z + Capability) : iProp Σ :=
      match reg with
      | R0 => reg_pointsTo reg0 v
      | R1 => reg_pointsTo reg1 v
      | R2 => reg_pointsTo reg2 v
      | R3 => reg_pointsTo reg3 v
      end.

    Lemma MinCaps_ptsreg_regtag_to_reg `{sailRegG Σ} (reg : RegName) (v : Z + Capability) :
      MinCaps_ptsreg reg v = reg_pointsTo (regtag_to_reg reg) v.
    Proof.
      by destruct reg.
    Qed.

    Definition region_addrs (b e : Addr) : list Addr :=
      filter (fun a => and (b ≤ a)%Z (a ≤ e)%Z) liveAddrs.

    Lemma element_of_region_addrs (a b e : Addr) :
      b ∈ liveAddrs → e ∈ liveAddrs →
      (b <= a)%Z /\ (a <= e)%Z ->
      a ∈ region_addrs b e.
    Proof.
      intros Hb He [Hba Hae].
      apply elem_of_list_filter.
      repeat (split; try assumption).
      apply elem_of_seqZ in Hb.
      apply elem_of_seqZ in He.
      apply elem_of_seqZ.
      lia.
    Qed.

    Context {Σ : gFunctors}.
    Notation D := ((leibnizO MemVal) -n> iPropO Σ). (* TODO: try -d>, drop leibnizO, might not need λne *)
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
             | H : _ ≡{_}≡ _ |-  _ => apply (discrete_iff _ _) in H
             | H : _ ≡ _ |-  _ => apply leibniz_equiv in H
             | _ => progress simplify_eq
             end;
      (* repeatedly apply congruence lemmas and use the equalities in the hypotheses. *)
      try (f_equiv; fast_done || auto_equiv).

    Ltac solve_proper ::= (repeat intros ?; simpl; auto_equiv).

    Program Definition MinCaps_ref_inv `{sailRegG Σ} `{invG Σ} {mG : memG Σ} (a : Addr) : D -n> iPropO Σ :=
      λne P, (∃ w, mapsto (hG := mc_ghG (mcMemG := mG)) a (DfracOwn 1) w ∗ P w)%I.
    Solve All Obligations with solve_proper.

    Program Definition MinCaps_csafe `{sailRegG Σ} `{invG Σ} {mG : memG Σ} (safe : D) : D :=
      λne w,
        (match w with
        | inr (MkCap O b e a) => True%I
        | inr (MkCap R b e a) =>
          (⌜ (b <= e)%Z ⌝ →
            ⌜ b ∈ liveAddrs /\ e ∈ liveAddrs ⌝ ∗
                                [∗ list] a ∈ (region_addrs b e), inv (mc_invNs (mcMemG := mG) .@ a) (MinCaps_ref_inv (mG := mG) a safe))
          ∨
          ⌜ (e < b)%Z ⌝
        | inr (MkCap RW b e a) =>
          (⌜ (b <= e)%Z ⌝ →
            ⌜ b ∈ liveAddrs /\ e ∈ liveAddrs ⌝ ∗
                                [∗ list] a ∈ (region_addrs b e), inv (mc_invNs (mcMemG := mG) .@ a) (MinCaps_ref_inv (mG := mG) a safe))
          ∨
          ⌜ (e < b)%Z ⌝
        | inl _ => False
        end)%I.

    Program Definition MinCaps_safe1 `{sailRegG Σ} `{invG Σ} {mG : memG Σ} (safe : D) : D :=
      λne w,
        (match w with
        | inl z => True
        | inr c => MinCaps_csafe (mG := mG) safe w
        end)%I.

    Global Instance MinCaps_csafe_contractive `{sailRegG Σ} `{invG Σ} {mG : memG Σ} :
      Contractive (MinCaps_csafe (mG := mG)).
    Proof.
      intros n x y Hdist w.
      unfold MinCaps_csafe.
      destruct w; first by intuition.
      destruct c.
      destruct cap_permission; first auto; solve_proper_prepare; solve_contractive.
    Qed.

    Global Instance MinCaps_safe1_contractive `{sailRegG Σ} `{invG Σ} {mG : memG Σ} :
      Contractive (MinCaps_safe1 (mG := mG)).
    Proof.
      intros n x y Hdist w.
      unfold MinCaps_safe1.
      destruct w; first by intuition.
      by apply MinCaps_csafe_contractive.
    Qed.

    Lemma fixpoint_MinCaps_safe1_eq `{sailRegG Σ} `{invG Σ} {mG : memG Σ} (w : leibnizO MemVal) :
      fixpoint (MinCaps_safe1 (mG := mG)) w ≡ MinCaps_safe1 (mG := mG) (fixpoint (MinCaps_safe1 (mG := mG))) w.
    Proof. exact: (fixpoint_unfold (MinCaps_safe1 (mG := mG)) w). Qed.

    Definition MinCaps_safe `{sailRegG Σ} `{invG Σ} {mG : memG Σ} : D :=
      λne w, (fixpoint (MinCaps_safe1 (mG := mG))) w.

    Lemma le_liveAddrs (a b e : Addr) :
      b ∈ liveAddrs ∧ e ∈ liveAddrs ->
      (b <= a)%Z ∧ (a <= e)%Z ->
      a ∈ liveAddrs.
    Proof.
      intros [Hb He] [Hba Hae].
      apply elem_of_seqZ in Hb.
      apply elem_of_seqZ in He.
      destruct Hb as [H0b Hbm].
      destruct He as [H0e Hem].
      rewrite elem_of_seqZ.
      split; lia.
    Qed.

    Lemma region_addrs_submseteq `{sailRegG Σ} `{invG Σ} {mG : memG Σ} (b' e' b e : Addr) :
      ⊢ ⌜ (b <= b')%Z /\ (e' <= e)%Z ⌝ -∗
                               ([∗ list] a ∈ (region_addrs b e), inv (mc_invNs (mcMemG := mG) .@ a) (∃ w, mapsto (hG := mc_ghG (mcMemG := mG)) a (DfracOwn 1) w ∗ fixpoint (MinCaps_safe1 (mG := mG)) w))%I -∗
                               ([∗ list] a ∈ (region_addrs b' e'), inv (mc_invNs (mcMemG := mG) .@ a) (∃ w, mapsto (hG := mc_ghG (mcMemG := mG)) a (DfracOwn 1) w ∗ fixpoint (MinCaps_safe1 (mG := mG)) w))%I.
    Proof.
      iIntros "[% %] Hregion".
      iApply (big_sepL_submseteq _ _ (region_addrs b e)).
      unfold region_addrs.
      induction liveAddrs.
      - cbn; trivial.
      - cbn.
        destruct (decide ((b' ≤ a)%Z ∧ (a ≤ e')%Z));
          destruct (decide ((b ≤ a)%Z ∧ (a ≤ e)%Z));
          trivial.
        + apply submseteq_skip; trivial.
        + destruct a0 as [Hb' He']; lia.
        + apply submseteq_cons; trivial.
      - iAssumption.
    Qed.

    Lemma safe_sub_range `{sailRegG Σ} `{invG Σ} {mG : memG Σ} (b' e' b e : Addr) :
      forall p a,
      ⊢ ⌜ (b <= b')%Z /\ (e' <= e)%Z ⌝ -∗
                               MinCaps_safe (mG := mG)
                               (inr {| cap_permission := p; cap_begin := b; cap_end := e; cap_cursor := a |}) -∗
                               MinCaps_safe (mG := mG)
                               (inr {| cap_permission := p; cap_begin := b'; cap_end := e'; cap_cursor := a |}).
    Proof.
      iIntros (p a) "/= [% %] Hsafe".
      do 2 rewrite fixpoint_MinCaps_safe1_eq.
      destruct p; try (by iFrame); simpl; iDestruct "Hsafe" as "/= [Hsafe | %]";
        try (iRight; iPureIntro; lia).
      - iLeft.
        iIntros "%".
        iAssert (⌜ (b <= e)%Z ⌝)%I as "-# Htmp".
        { iPureIntro; lia. }
        iAssert (
          ⌜b ∈ liveAddrs ∧ e ∈ liveAddrs⌝
                             ∗ ([∗ list] a0 ∈ region_addrs b e, inv (mc_invNs.@a0)
                                                                    (∃ w,
                                                                        mapsto a0 (DfracOwn 1) w
                                                                               ∗ fixpoint MinCaps_safe1 w))
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
        iAssert (⌜ (b <= e)%Z ⌝)%I as "-# Htmp".
        { iPureIntro; lia. }
        iAssert (
          ⌜b ∈ liveAddrs ∧ e ∈ liveAddrs⌝
                             ∗ ([∗ list] a0 ∈ region_addrs b e, inv (mc_invNs.@a0)
                                                                    (∃ w,
                                                                        mapsto a0 (DfracOwn 1) w
                                                                               ∗ fixpoint MinCaps_safe1 w))
        )%I with "[Htmp Hsafe]" as "Hsafe".
        { iApply ("Hsafe" with "Htmp"). }
        iDestruct "Hsafe" as "[% H]".
        iSplitR.
        + iPureIntro; split.
          apply (le_liveAddrs H4 (conj H1 (Z.le_trans b' e' e H3 H2))).
          apply (le_liveAddrs H4 (conj (Z.le_trans b b' e' H1 H3) H2)).
        + iApply (region_addrs_submseteq $! (conj H1 H2) with "H").
    Qed.

    Lemma specialize_range `{sailRegG Σ} `{invG Σ} {mG : memG Σ} (b e addr : Addr) :
      ⊢ ⌜ (b <= addr)%Z /\ (addr <= e)%Z ⌝ -∗
        (⌜ b ∈ liveAddrs /\ e ∈ liveAddrs ⌝ ∗
          [∗ list] a ∈ (region_addrs b e), inv (mc_invNs (mcMemG := mG) .@ a) (∃ w, mapsto (hG := mc_ghG (mcMemG := mG)) a (DfracOwn 1) w ∗ fixpoint (MinCaps_safe1 (mG := mG)) w))%I -∗
        (inv (mc_invNs (mcMemG := mG) .@ addr) (∃ w, mapsto (hG := mc_ghG (mcMemG := mG)) addr (DfracOwn 1) w ∗ fixpoint (MinCaps_safe1 (mG := mG)) w))%I.
    Proof.
      iIntros "[% %] [[% %] Hrange]".
      iApply (big_sepL_elem_of with "Hrange").
      apply element_of_region_addrs; try assumption.
      split; assumption.
    Qed.

    Definition GPRs : list RegName := finite.enum RegName.

    Definition interp_gprs `{sailRegG Σ} `{invG Σ} `{mG : memG Σ} : iProp Σ :=
      [∗ list] r ∈ GPRs, (∃ w, MinCaps_ptsreg r w ∗ MinCaps_safe (mG := mG) w)%I.

    Import env.notations.

    Definition luser_inst `{sailRegG Σ} `{invG Σ} (mG : memG Σ) (p : Predicate) (ts : Env Val (𝑯_Ty p)) : iProp Σ :=
      (match p return Env Val (𝑯_Ty p) -> iProp Σ with
      | ptsreg => fun ts => MinCaps_ptsreg (env.head (env.tail ts)) (env.head ts)
      | ptsto => fun ts => mapsto (hG := mc_ghG (mcMemG := mG)) (env.head (env.tail ts)) (DfracOwn 1) (env.head ts)
      | safe => fun ts => MinCaps_safe (mG := mG) (env.head ts)
      | dummy => fun ts => True%I
      | gprs => fun ts => interp_gprs (mG := mG)
      end) ts.

    Global Instance MinCaps_safe_Persistent `{sailRegG Σ} `{invG Σ} {mG : memG Σ} (w : leibnizO MemVal) : Persistent (MinCaps_safe (mG := mG) w).
    Proof. destruct w; simpl; rewrite fixpoint_MinCaps_safe1_eq; simpl; first apply _.
           destruct c; destruct cap_permission; apply _. Qed.

    Definition lduplicate_inst `{sailRegG Σ} `{invG Σ} (mG : memG Σ) :
      forall (p : Predicate) (ts : Env Val (𝑯_Ty p)),
        is_duplicable p = true ->
        (luser_inst mG p ts) ⊢ (luser_inst mG p ts ∗ luser_inst mG p ts).
    Proof.
      iIntros (p ts hdup) "H".
      destruct p; inversion hdup;
      iDestruct "H" as "#H";
      auto.
    Qed.

    End WithIrisNotations.
  End MinCapsIrisHeapKit.

  Module Import MinCapsIrisInstance := IrisInstance MinCapsIrisHeapKit.

  Section Lemmas.
    Context `{sg : sailG Σ}.

    Lemma gen_dummy_sound :
      ValidLemma MinCapsSpecification.lemma_gen_dummy.
    Proof.
      intros ι. destruct_syminstance ι. cbn.
      auto.
    Qed.

    Lemma open_ptsreg_sound :
      ValidLemma MinCapsSpecification.lemma_open_ptsreg.
    Proof.
      intros ι. destruct_syminstance ι. cbn.
      destruct reg; auto.
    Qed.

    Lemma close_ptsreg_sound {R} :
      ValidLemma (MinCapsSpecification.lemma_close_ptsreg R).
    Proof.
      intros ι. destruct_syminstance ι. cbn.
      rewrite MinCapsIrisHeapKit.MinCaps_ptsreg_regtag_to_reg; auto.
    Qed.

    Lemma open_gprs_sound :
      ValidLemma (MinCapsSpecification.lemma_open_gprs).
    Proof.
      intros ι; destruct_syminstance ι; cbn.
      iIntros "[HR0 [HR1 [HR2 [HR3 _]]]]".
      iSplitL "HR0"; try done.
      iSplitL "HR1"; try done.
      iSplitL "HR2"; try done.
    Qed.

    Lemma close_gprs_sound :
      ValidLemma (MinCapsSpecification.lemma_close_gprs).
    Proof.
      intros ι; destruct_syminstance ι; cbn.
      iIntros "[HR0 [HR1 [HR2 HR3]]]".
      iSplitL "HR0"; try done.
      iSplitL "HR1"; try done.
      iSplitL "HR2"; try done.
      iSplitL "HR3"; try done.
    Qed.

    Lemma int_safe_sound :
      ValidLemma MinCapsSpecification.lemma_int_safe.
    Proof.
      intros ι. destruct_syminstance ι. cbn.
      rewrite MinCapsIrisHeapKit.fixpoint_MinCaps_safe1_eq; auto.
    Qed.

    (* Lemma duplicate_safe_sound : *)
    (*   ValidLemma MinCapsSpecification.lemma_duplicate_safe. *)
    (* Proof. *)
    (*   intros ι. destruct_syminstance ι. cbn. *)
    (*   iIntros "#Hsafe". now iSplit. *)
    (* Qed. *)

    Lemma safe_move_cursor_sound :
      ValidLemma MinCapsSpecification.lemma_safe_move_cursor.
    Proof.
      intros ι. destruct_syminstance ι. cbn.
      iIntros "#Hsafe".
      iSplit; [done|].
      do 2 rewrite MinCapsIrisHeapKit.fixpoint_MinCaps_safe1_eq.
      unfold MinCapsIrisHeapKit.MinCaps_safe1.
      destruct p; auto.
    Qed.

    Lemma safe_sub_perm_sound :
      ValidLemma MinCapsSpecification.lemma_safe_sub_perm.
    Proof.
      intros ι. destruct_syminstance ι. cbn.
      iIntros "[#Hsafe %Hp]".
      iSplit; [done|].
      do 2 rewrite MinCapsIrisHeapKit.fixpoint_MinCaps_safe1_eq.
      destruct p; destruct p'; trivial;
        destruct Hp; discriminate.
    Qed.

    Lemma safe_within_range_sound :
      ValidLemma MinCapsSpecification.lemma_safe_within_range.
    Proof.
      intros ι. destruct_syminstance ι. cbn.
      iIntros "[#Hsafe [_ Hp]]".
      iSplit; [done|].
      iDestruct "Hp" as (H) "_".
      unfold is_true in H;
        apply andb_prop in H;
        destruct H as [Hb He];
        apply Zle_is_le_bool in Hb;
        apply Zle_is_le_bool in He.
      iApply (MinCapsIrisHeapKit.safe_sub_range $! (conj Hb He) with "Hsafe").
    Qed.

  End Lemmas.

  Lemma dI_sound `{sg : sailG Σ} `{invG} {Γ es δ} :
    forall code : Val ty_int,
    evals es δ = env.snoc env.nil (MkB _ ty_int) code
    → ⊢ semTriple δ (⌜is_true true⌝ ∧ emp) (stm_foreign dI es)
          (λ (v : Val ty_instr) (δ' : CStore Γ),
             (⌜is_true true⌝ ∧ emp) ∗ ⌜δ' = δ⌝).
  Proof.
    intros code Heq.
    iApply iris_rule_noop; try done.
    intros s' γ γ' μ μ' δ' step.
    dependent elimination step.
    rewrite Heq in f1.
    cbn in f1. destruct f1 as [res' e].
    dependent elimination e.
    repeat split; destruct res; eauto.
  Qed.

  Import iris.base_logic.lib.gen_heap.

  Lemma rM_sound `{sg : sailG Σ} `{invG} {Γ es δ} :
    forall a (p : Val ty_perm) (b e : Val ty_addr),
      evals es δ = env.snoc env.nil (MkB _ ty_addr) a ->
    ⊢ semTriple δ
        (MinCapsIrisHeapKit.MinCaps_safe (mG := sailG_memG)
           (inr {| cap_permission := p; cap_begin := b; cap_end := e; cap_cursor := a |})
         ∗ (⌜Subperm R p⌝ ∧ emp) ∗ ⌜(b <=? a)%Z && (a <=? e)%Z = true⌝ ∧ emp)
        (stm_foreign rM es)%env
        (λ (v : Z + Capability) (δ' : CStore Γ),
           (MinCapsIrisHeapKit.MinCaps_safe (mG := sailG_memG) v) ∗ ⌜δ' = δ⌝).
  Proof.
    intros a p b e Heq.
    iIntros "[#Hsafe [[%Hsubp _] [%Hbounds _]]]".
    apply andb_prop in Hbounds as [Hb%Zle_is_le_bool He%Zle_is_le_bool].
    rewrite wp_unfold.
    destruct p; try discriminate.
    (* TODO: clean this up! *)
    - iAssert (inv (MinCapsIrisHeapKit.mc_invNs.@a) (∃ w, gen_heap.mapsto a (dfrac.DfracOwn 1) w ∗ MinCapsIrisHeapKit.MinCaps_safe w))%I as "Hown".
      { rewrite MinCapsIrisHeapKit.fixpoint_MinCaps_safe1_eq; simpl.
        iDestruct "Hsafe" as "[Hsafe | %]"; try lia.
        iAssert (⌜ (b <= e)%Z ⌝)%I as "-# Htmp".
        { iPureIntro; lia. }
        iAssert (
          ⌜b ∈ MinCapsIrisHeapKit.liveAddrs ∧ e ∈ MinCapsIrisHeapKit.liveAddrs⌝
                             ∗ ([∗ list] a0 ∈ MinCapsIrisHeapKit.region_addrs b e,
                                inv (MinCapsIrisHeapKit.mc_invNs.@a0) (∃ w, mapsto a0 (DfracOwn 1) w
                                                        ∗ fixpoint MinCapsIrisHeapKit.MinCaps_safe1 w))
        )%I with "[Htmp Hsafe]" as "Hsafe'".
        { iApply ("Hsafe" with "Htmp"). }
        iApply (MinCapsIrisHeapKit.specialize_range $! (conj Hb He) with "Hsafe'"). }
      iIntros (σ' ks1 ks n) "[Hregs Hmem]".
      iDestruct "Hmem" as (memmap) "[Hmem' %]".
      iInv "Hown" as "Hinv" "Hclose".
      iMod (fupd_mask_subseteq empty) as "Hclose2"; first set_solver.
      iModIntro.
      iSplitR; first by intuition.
      iIntros (e2 σ'' efs) "%".
      cbn in H1.
      dependent elimination H1.
      dependent elimination s.
      cbn in f1.
      dependent elimination f1.
      do 2 iModIntro.
      iDestruct "Hinv" as (v) "Hav".
      iDestruct "Hav" as "[Hav #Hrec]".
      iAssert (⌜ memmap !! a = Some v ⌝)%I with "[Hav Hmem']" as "%".
      { iApply (gen_heap.gen_heap_valid with "Hmem' Hav"). }
      iMod "Hclose2" as "_".
      iAssert (▷ (∃ v0 : Z + Capability, gen_heap.mapsto a (dfrac.DfracOwn 1) v0 ∗ fixpoint MinCapsIrisHeapKit.MinCaps_safe1 v0))%I with "[Hav Hrec]" as "Hinv".
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
      simpl in H0. subst. rewrite Heq.
      iAssumption.
    - iAssert (inv (MinCapsIrisHeapKit.mc_invNs.@a) (∃ w, gen_heap.mapsto a (dfrac.DfracOwn 1) w ∗ fixpoint (MinCapsIrisHeapKit.MinCaps_safe1) w))%I as "Hown".
      { rewrite MinCapsIrisHeapKit.fixpoint_MinCaps_safe1_eq; simpl.
        iDestruct "Hsafe" as "[Hsafe | %]"; try lia.
        iAssert (⌜ (b <= e)%Z ⌝)%I as "-# Htmp".
        { iPureIntro; lia. }
        iAssert (
          ⌜b ∈ MinCapsIrisHeapKit.liveAddrs ∧ e ∈ MinCapsIrisHeapKit.liveAddrs⌝
                             ∗ ([∗ list] a0 ∈ MinCapsIrisHeapKit.region_addrs b e,
                                inv (MinCapsIrisHeapKit.mc_invNs.@a0) (∃ w, mapsto a0 (DfracOwn 1) w
                                                        ∗ fixpoint MinCapsIrisHeapKit.MinCaps_safe1 w))
        )%I with "[Htmp Hsafe]" as "Hsafe'".
        { iApply ("Hsafe" with "Htmp"). }
        iApply (MinCapsIrisHeapKit.specialize_range $! (conj Hb He) with "Hsafe'"). }
      iIntros (σ' ks1 ks n) "[Hregs Hmem]".
      iDestruct "Hmem" as (memmap) "[Hmem' %]".
      iInv "Hown" as "Hinv" "Hclose".
      iMod (fupd_mask_subseteq empty) as "Hclose2"; first set_solver.
      iModIntro.
      iSplitR; first by intuition.
      iIntros (e2 σ'' efs) "%".
      cbn in H1.
      dependent elimination H1.
      dependent elimination s.
      cbn in f1.
      dependent elimination f1.
      do 2 iModIntro.
      iDestruct "Hinv" as (v) "Hav".
      iDestruct "Hav" as "[Hav #Hrec]".
      iAssert (⌜ memmap !! a = Some v ⌝)%I with "[Hav Hmem']" as "%".
      { iApply (gen_heap.gen_heap_valid with "Hmem' Hav"). }
      iMod "Hclose2" as "_".
      iAssert (▷ (∃ v0 : Z + Capability, gen_heap.mapsto a (dfrac.DfracOwn 1) v0 ∗ fixpoint MinCapsIrisHeapKit.MinCaps_safe1 v0))%I with "[Hav Hrec]" as "Hinv".
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
      simpl in H0. subst. rewrite Heq.
      iAssumption.
  Qed.

  Lemma wM_sound `{sg : sailG Σ} `{invG} {Γ es δ} :
    forall a w (p : Val ty_perm) (b e : Val ty_addr),
      evals es δ = env.snoc (env.snoc env.nil (MkB _ ty_addr) a)
                            (MkB _ ty_memval) w
    → ⊢ semTriple δ
        (MinCapsIrisHeapKit.MinCaps_safe (mG := sailG_memG) w
         ∗ MinCapsIrisHeapKit.MinCaps_safe (mG := sailG_memG)
                                          (inr {|
                                               cap_permission := p;
                                               cap_begin := b;
                                               cap_end := e;
                                               cap_cursor := a |})
         ∗ (⌜ Subperm RW p ⌝ ∧ emp)
         ∗ ⌜is_true ((b <=? a)%Z && (a <=? e)%Z)⌝ ∧ emp)
        (stm_foreign wM es)
        (λ (v3 : ()) (δ' : CStore Γ),
         (⌜v3 = tt⌝ ∧ emp) ∗ ⌜δ' = δ⌝).
    Proof.
      intros a w p b e Heq.
      iIntros "[#Hwsafe [#Hsafe [[%Hsubp _] [%Hbounds _]]]]".
      apply andb_prop in Hbounds as [Hb%Zle_is_le_bool He%Zle_is_le_bool].
      rewrite wp_unfold.
      destruct p; try discriminate. clear Hsubp.
      iIntros (σ' ks1 ks n) "[Hregs Hmem]".
      iDestruct "Hmem" as (memmap) "[Hmem' %]".
      iAssert (inv (MinCapsIrisHeapKit.mc_invNs.@a) (∃ w, gen_heap.mapsto a (dfrac.DfracOwn 1) w ∗ fixpoint (MinCapsIrisHeapKit.MinCaps_safe1) w))%I as "Hown".
      { do 2 rewrite MinCapsIrisHeapKit.fixpoint_MinCaps_safe1_eq; simpl.
        iDestruct "Hsafe" as "[Hsafe | %]"; try lia.
        iAssert (⌜ (b <= e)%Z ⌝)%I as "-# Htmp".
        { iPureIntro; lia. }
        iAssert (
          ⌜b ∈ MinCapsIrisHeapKit.liveAddrs ∧ e ∈ MinCapsIrisHeapKit.liveAddrs⌝
                             ∗ ([∗ list] a0 ∈ MinCapsIrisHeapKit.region_addrs b e,
                                inv (MinCapsIrisHeapKit.mc_invNs.@a0) (∃ w, mapsto a0 (DfracOwn 1) w
                                                        ∗ fixpoint MinCapsIrisHeapKit.MinCaps_safe1 w))
        )%I with "[Htmp Hsafe]" as "Hsafe'".
        { iApply ("Hsafe" with "Htmp"). }
        iApply (MinCapsIrisHeapKit.specialize_range $! (conj Hb He) with "Hsafe'"). }
      iInv "Hown" as "Hinv" "Hclose".
      iMod (fupd_mask_subseteq empty) as "Hclose2"; first set_solver.
      iModIntro.
      iSplitR; first by intuition.
      iIntros (e2 σ'' efs) "%".
      cbn in H1.
      dependent elimination H1.
      dependent elimination s.
      rewrite Heq in f1.
      cbn in f1.
      dependent elimination f1.
      do 2 iModIntro.
      iDestruct "Hinv" as (v) "Hav".
      iDestruct "Hav" as "[Hav Hrec]".
      iMod (gen_heap.gen_heap_update _ _ _ w with "Hmem' Hav") as "[Hmem' Hav]".
      iMod "Hclose2" as "_".
      iAssert (▷ (∃ v0 : Z + Capability, gen_heap.mapsto a (dfrac.DfracOwn 1) v0 ∗ fixpoint MinCapsIrisHeapKit.MinCaps_safe1 v0))%I with "[Hav Hrec]" as "Hinv".
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

  Lemma foreignSem `{sg : sailG Σ} : ForeignSem (Σ := Σ).
  Proof.
    intros Γ τ Δ f es δ.
    destruct f; cbn - [MinCapsIrisHeapKit.MinCaps_safe MinCapsIrisHeapKit.MinCaps_csafe];
      intros ι; destruct_syminstance ι;
        eauto using dI_sound, rM_sound, wM_sound.
  Qed.

  Lemma lemSem `{sg : sailG Σ} : LemmaSem (Σ := Σ).
  Proof.
    intros Δ []; eauto using
      open_ptsreg_sound, close_ptsreg_sound,
      open_gprs_sound, close_gprs_sound, int_safe_sound,
      safe_move_cursor_sound, safe_sub_perm_sound,
      safe_within_range_sound, gen_dummy_sound.
  Qed.

End MinCapsModel.
