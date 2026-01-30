theory Example_ECtHR_Article6_Final
  imports DDL_automation
begin

consts
  criminal_charge :: "\<sigma>"
  fair_hearing :: "\<sigma>"
  public_hearing :: "\<sigma>"
  reasonable_time :: "\<sigma>"
  independent_tribunal :: "\<sigma>"
  impartial_tribunal :: "\<sigma>"
  established_by_law :: "\<sigma>"

  public_judgment :: "\<sigma>"
  morals :: "\<sigma>"
  public_order :: "\<sigma>"
  national_security :: "\<sigma>"
  juvenile_interest :: "\<sigma>"
  private_life :: "\<sigma>"
  interests_of_justice :: "\<sigma>"

  presumed_innocent :: "\<sigma>"
  proved_guilty :: "\<sigma>"

  Informed_Promptly :: "\<sigma>"
  In_Language :: "\<sigma>"
  In_Detail :: "\<sigma>"
  Adequate_Time :: "\<sigma>"
  Adequate_Facilities :: "\<sigma>"
  Defend_Self :: "\<sigma>"
  Legal_Assistance_SelfChosen :: "\<sigma>"
  Has_Means :: "\<sigma>"
  Justice_Requires :: "\<sigma>"
  Free_Legal_Assistance :: "\<sigma>"
  Examine_Witness_Against :: "\<sigma>"
  Obtain_Defense_Witness :: "\<sigma>"
  Equal_Conditions :: "\<sigma>"
  Understands_Lang :: "\<sigma>"
  Speaks_Lang :: "\<sigma>"
  Free_Interpreter :: "\<sigma>"

definition article6_fair_hearing :: "rule" where
  "article6_fair_hearing = ({criminal_charge}, PE fair_hearing)"

definition article6_public_hearing :: "rule" where
  "article6_public_hearing = ({criminal_charge}, PE public_hearing)"

definition article6_reasonable_time :: "rule" where
  "article6_reasonable_time = ({criminal_charge}, PE reasonable_time)"

definition article6_independent_tribunal :: "rule" where
  "article6_independent_tribunal = ({criminal_charge}, PE independent_tribunal)"

definition article6_impartial_tribunal :: "rule" where
  "article6_impartial_tribunal = ({criminal_charge}, PE impartial_tribunal)"

definition article6_established_by_law :: "rule" where
  "article6_established_by_law = ({criminal_charge}, PE established_by_law)"

definition article6_public_judgment :: "rule" where
  "article6_public_judgment = ({}, PE public_judgment)"

definition article6_public_exception :: "rule" where
  "article6_public_exception =
     ({morals, public_order, national_security, juvenile_interest,
       private_life, interests_of_justice}, PE (\<^bold>\<not> public_judgment))"

definition article6_presumption_rule :: "rule" where
  "article6_presumption_rule = ({criminal_charge}, PE presumed_innocent)"

definition article6_exception_rule :: "rule" where
  "article6_exception_rule = ({proved_guilty}, PE (\<^bold>\<not> presumed_innocent))"

definition article6a_info :: "rule" where
  "article6a_info = ({criminal_charge},
     PE (Informed_Promptly \<^bold>\<and> In_Language \<^bold>\<and> In_Detail))"

definition article6b_defense :: "rule" where
  "article6b_defense = ({criminal_charge},
     PE (Adequate_Time \<^bold>\<and> Adequate_Facilities))"

definition article6c_right :: "rule" where
  "article6c_right = ({criminal_charge},
     PE (Defend_Self \<^bold>\<or> Legal_Assistance_SelfChosen))"

definition article6c_exception_right :: "rule" where
  "article6c_exception_right =
     ({criminal_charge, \<^bold>\<not>Has_Means, Justice_Requires},
      PE Free_Legal_Assistance)"

definition article6d_witness :: "rule" where
  "article6d_witness = ({criminal_charge},
     PE (Examine_Witness_Against \<^bold>\<and> Obtain_Defense_Witness \<^bold>\<and> Equal_Conditions))"

definition article6e_interpreter :: "rule" where
  "article6e_interpreter =
     ({criminal_charge, (\<^bold>\<not>Understands_Lang \<^bold>\<or> \<^bold>\<not>Speaks_Lang)},
      PE Free_Interpreter)"

axiomatization where
  (*frame reflexivity*)
  frame_reflexive: "reflexive N_OBL" and
  
  (*rules in the permission rule set*)
  r6_fair_hearing_in_PER: "article6_fair_hearing \<in> R_PER" and
  r6_public_hearing_in_PER: "article6_public_hearing \<in> R_PER" and
  r6_reasonable_time_in_PER: "article6_reasonable_time \<in> R_PER" and
  r6_independent_tribunal_in_PER: "article6_independent_tribunal \<in> R_PER" and
  r6_impartial_tribunal_in_PER: "article6_impartial_tribunal \<in> R_PER" and
  r6_established_by_law_in_PER: "article6_established_by_law \<in> R_PER" and
  rule_public_judgment_in_PER: "article6_public_judgment \<in> R_PER" and
  rule_public_exception_in_PER: "article6_public_exception \<in> R_PER" and
  article6_public_suprel: "(article6_public_exception, article6_public_judgment) \<in> sup_rel" and
  rule_presumption_in_PER: "article6_presumption_rule \<in> R_PER" and
  rule_exception_in_PER: "article6_exception_rule \<in> R_PER" and
  article6_suprel_presumption: "(article6_exception_rule, article6_presumption_rule) \<in> sup_rel" and
  rule_6a_in_PER: "article6a_info \<in> R_PER" and
  rule_6b_in_PER: "article6b_defense \<in> R_PER" and
  rule_6c1_in_PER: "article6c_right \<in> R_PER" and
  rule_6c2_in_PER: "article6c_exception_right \<in> R_PER" and
  rule_6d_in_PER: "article6d_witness \<in> R_PER" and
  rule_6e_in_PER: "article6e_interpreter \<in> R_PER" and

  (*applicable axioms*)
  applicable_fair_hearing: "applicable article6_fair_hearing" and
  applicable_public_hearing: "applicable article6_public_hearing" and
  applicable_reasonable_time: "applicable article6_reasonable_time" and
  applicable_independent_tribunal: "applicable article6_independent_tribunal" and
  applicable_impartial_tribunal: "applicable article6_impartial_tribunal" and
  applicable_established_by_law: "applicable article6_established_by_law" and
  applicable_presumption: "applicable article6_presumption_rule" and
  applicable_exception: "applicable article6_exception_rule" and

  (*case facts*)
  fact_criminal_charge: "criminal_charge \<in> F" and
  fact_proved_guilty: "proved_guilty \<in> F" and
  fact_no_reasonable_time: "reasonable_time \<notin> F" and
  fact_no_fair_hearing: "fair_hearing \<notin> F" and
  fact_no_public_hearing: "public_hearing \<notin> F" and
  fact_no_independent_tribunal: "independent_tribunal \<notin> F" and
  fact_no_impartial_tribunal: "impartial_tribunal \<notin> F" and
  fact_no_established_by_law: "established_by_law \<notin> F"

(*Facts are not modal formulas*)
axiomatization where
  fact_not_modal_1[simp]: "criminal_charge \<noteq> PE a" and
  fact_not_modal_2[simp]: "proved_guilty \<noteq> PE a" and
  fact_not_modal_3[simp]: "fair_hearing \<noteq> PE a" and
  fact_not_modal_4[simp]: "public_hearing \<noteq> PE a" and
  fact_not_modal_5[simp]: "reasonable_time \<noteq> PE a" and
  fact_not_modal_6[simp]: "independent_tribunal \<noteq> PE a" and
  fact_not_modal_7[simp]: "impartial_tribunal \<noteq> PE a" and
  fact_not_modal_8[simp]: "established_by_law \<noteq> PE a" and
  fact_not_modal_9[simp]: "presumed_innocent \<noteq> PE a" and
  fact_not_neg_modal_1[simp]: "criminal_charge \<noteq> (\<lambda>w. \<not> (PE a w))" and
  fact_not_neg_modal_2[simp]: "proved_guilty \<noteq> (\<lambda>w. \<not> (PE a w))" and
  fact_not_neg_modal_3[simp]: "fair_hearing \<noteq> (\<lambda>w. \<not> (PE a w))" and
  fact_not_neg_modal_4[simp]: "public_hearing \<noteq> (\<lambda>w. \<not> (PE a w))" and
  fact_not_neg_modal_5[simp]: "reasonable_time \<noteq> (\<lambda>w. \<not> (PE a w))" and
  fact_not_neg_modal_6[simp]: "independent_tribunal \<noteq> (\<lambda>w. \<not> (PE a w))" and
  fact_not_neg_modal_7[simp]: "impartial_tribunal \<noteq> (\<lambda>w. \<not> (PE a w))" and
  fact_not_neg_modal_8[simp]: "established_by_law \<noteq> (\<lambda>w. \<not> (PE a w))" and
  fact_not_neg_modal_9[simp]: "presumed_innocent \<noteq> (\<lambda>w. \<not> (PE a w))"

(*Violation of a permission*)
definition violated_permission :: "\<sigma> \<Rightarrow> bool" where
  "violated_permission \<phi> \<equiv> \<turnstile>\<^sub>P\<^sub>E \<phi> \<and> \<phi> \<notin> F"

lemma case_facts_derivable:
  shows "criminal_charge \<in> F \<and>
         proved_guilty \<in> F \<and>
         reasonable_time \<notin> F \<and>
         fair_hearing \<notin> F \<and>
         public_hearing \<notin> F \<and>
         independent_tribunal \<notin> F \<and>
         impartial_tribunal \<notin> F \<and>
         established_by_law \<notin> F"
   sledgehammer
   using fact_proved_guilty fact_criminal_charge fact_no_fair_hearing fact_no_public_hearing fact_no_reasonable_time fact_no_established_by_law fact_no_impartial_tribunal fact_no_independent_tribunal by simp

lemma consistency_check:
  True
  nitpick [satisfy, user_axioms, show_all] oops

lemma fair_hearing_applicable:
  shows "\<turnstile>\<^sub>P\<^sub>E fair_hearing"   
  sledgehammer
  by (metis applicable_fair_hearing article6_fair_hearing_def derives_permission_from_rule fact_no_fair_hearing
      r6_fair_hearing_in_PER snd_eqD)

lemma fair_hearing_violation:
  assumes "criminal_charge \<in> F"
      and "fair_hearing \<notin> F"
  shows "violated_permission fair_hearing"
   sledgehammer
   using fair_hearing_applicable violated_permission_def fact_no_fair_hearing by simp

lemma reasonable_time_applicable:
  shows "\<turnstile>\<^sub>P\<^sub>E reasonable_time"
   sledgehammer
   by (metis applicable_reasonable_time article6_reasonable_time_def derives_permission_from_rule fact_no_reasonable_time
       r6_reasonable_time_in_PER snd_conv)

lemma reasonable_time_violation:
  assumes "criminal_charge \<in> F"
      and "reasonable_time \<notin> F"
  shows "violated_permission reasonable_time"
   sledgehammer
   using reasonable_time_applicable violated_permission_def fact_no_reasonable_time by simp

lemma public_hearing_applicable:
  shows "\<turnstile>\<^sub>P\<^sub>E public_hearing"
   sledgehammer
   by (metis applicable_public_hearing article6_public_hearing_def derives_permission_from_rule fact_no_public_hearing
       r6_public_hearing_in_PER snd_conv)

lemma public_hearing_violation:
  assumes "criminal_charge \<in> F"
      and "public_hearing \<notin> F"
  shows "violated_permission public_hearing"
  sledgehammer
  using public_hearing_applicable violated_permission_def case_facts_derivable by simp

lemma independent_tribunal_applicable:
  shows "\<turnstile>\<^sub>P\<^sub>E independent_tribunal" 
   sledgehammer
   by (metis fact_no_independent_tribunal article6_independent_tribunal_def r6_independent_tribunal_in_PER applicable_independent_tribunal derives_permission_from_rule snd_conv)

lemma independent_tribunal_violation:
  assumes "criminal_charge \<in> F"
      and "independent_tribunal \<notin> F"
  shows "violated_permission independent_tribunal"
   sledgehammer
   using independent_tribunal_applicable violated_permission_def case_facts_derivable by simp

lemma impartial_tribunal_applicable:
  shows "\<turnstile>\<^sub>P\<^sub>E impartial_tribunal"
   sledgehammer
   by (metis applicable_impartial_tribunal article6_impartial_tribunal_def derives_permission_from_rule
       fact_no_impartial_tribunal r6_impartial_tribunal_in_PER snd_conv)

lemma impartial_tribunal_violation:
  assumes "criminal_charge \<in> F"
      and "impartial_tribunal \<notin> F"
  shows "violated_permission impartial_tribunal"
   sledgehammer
   using impartial_tribunal_applicable violated_permission_def case_facts_derivable by simp

lemma established_by_law_applicable:
  shows "\<turnstile>\<^sub>P\<^sub>E established_by_law"
   sledgehammer
   by (metis applicable_established_by_law article6_established_by_law_def derives_permission_from_rule
       fact_no_established_by_law r6_established_by_law_in_PER snd_conv)

lemma presumption_innocence_applicable:
  assumes "presumed_innocent \<notin> F"
  shows "\<turnstile>\<^sub>P\<^sub>E presumed_innocent"
   sledgehammer
   by (metis applicable_presumption article6_presumption_rule_def assms derives_permission_from_rule
       rule_presumption_in_PER snd_conv)

(*Once guilt is proved, permission to treat as not innocent*)
lemma exception_to_presumption_applicable:
  assumes "(\<^bold>\<not> presumed_innocent) \<notin> F"
  shows "\<turnstile>\<^sub>P\<^sub>E (\<^bold>\<not> presumed_innocent)"
   sledgehammer
   by (metis applicable_exception article6_exception_rule_def assms derives_permission_from_rule rule_exception_in_PER
       snd_conv)

(*CTD consistency between presumption of innocence and its exception*)
theorem Article6_CTD_consistency:
  shows "article6_exception_rule >r article6_presumption_rule"
  sledgehammer
  using article6_suprel_presumption by fastforce

(*All core guarantees of paragraph 1 are violated in this case*)
theorem Article6_all_violations:
  shows "violated_permission fair_hearing \<and>
         violated_permission reasonable_time \<and>
         violated_permission public_hearing \<and>
         violated_permission independent_tribunal \<and>
         violated_permission impartial_tribunal" 
   sledgehammer
   using violated_permission_def fair_hearing_applicable public_hearing_applicable reasonable_time_applicable fact_no_fair_hearing impartial_tribunal_applicable fact_no_reasonable_time fact_no_public_hearing independent_tribunal_applicable fact_no_independent_tribunal fact_no_impartial_tribunal by simp

theorem Article6_case_summary:
  shows "criminal_charge \<in> F \<and> proved_guilty \<in> F \<and>
         violated_permission fair_hearing \<and>
         violated_permission reasonable_time \<and>
         violated_permission public_hearing \<and>
         violated_permission independent_tribunal \<and>
         violated_permission impartial_tribunal"
   sledgehammer
   using fact_proved_guilty fact_criminal_charge Article6_all_violations by simp

end
