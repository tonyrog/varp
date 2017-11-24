//   Program for controling the wheel functions in an aircraft
//   (Exampel provided by SAAB flygdivision)
//   Translated into ulisp by Tony Rogvall @ Logikkonsult NP AB
//

// In prameters form other units
//typedef unsigned bool:1;
typedef unsigned bool;

#define false 0
#define true  1

// UNIT NOSSTALL

bool nosstall_inne1 = false;
bool nosstall_inne2 = false;
bool nosstall_ute1  = false;
bool nosstall_ute2  = false;
bool nosstall_infj1 = false;
bool nosstall_infj2 = false;
bool nosstall_utfj1 = false;
bool nosstall_utfj2 = false;
bool nosstall_lucka_oppen1 = false;
bool nosstall_lucka_oppen2 = false;
bool nosstall_lucka_stangd1 = false;
bool nosstall_lucka_stangd2 = false;

// UNIT HSTALL_H

bool hstall_h_inne1 = false;
bool hstall_h_inne2 = false;
bool hstall_h_ute1 = false;
bool hstall_h_ute2 = false;
bool hstall_h_infj1 = false;
bool hstall_h_infj2 = false;
// bool hstall_h_utfj1;
// bool hstall_h_utfj2;
bool hstall_h_lucka_oppen1 = false;
bool hstall_h_lucka_oppen2 = false;
bool hstall_h_lucka_stangd1 = false;
bool hstall_h_lucka_stangd2 = false;

// UNIT HSTALL_V

bool hstall_v_inne1 = false;
bool hstall_v_inne2 = false;
bool hstall_v_ute1 = false;
bool hstall_v_ute2 = false;
bool hstall_v_infj1 = false;
bool hstall_v_infj2 = false;
//  bool hstall_v_utfj1 = false;
//  bool hstall_v_utfj2 = false;
bool hstall_v_lucka_oppen1 = false;
bool hstall_v_lucka_oppen2 = false;
bool hstall_v_lucka_stangd1 = false;
bool hstall_v_lucka_stangd2 = false;

// STATE variables

bool alla_luckor_oppna = false;
bool alla_luckor_stangda = false;
bool alla_stall_inne = false;
bool alla_stall_ute  = false;
bool alla_stall_infj  = false;
bool alla_stall_utfj   = false;
bool nosstall_utfj  = false;
bool hstall_utfj   = false;
bool hstall_infj   = false;
bool utfallning_tillaten  = false;
bool infallning_tillaten  = false;
bool spin_down  = false;
bool spak_hant_ok   = false;
bool landst_regl_fel  = false;

// ACTION variables

bool stallmanover_pagar   = false;
bool luckmanover_pagar  = false;
bool utfallning_pagar  = false;
bool infallning_pagar  = false;

// Externals not defined (may be in variables)
bool forsorjning_av_kritiska_blocket_ok   = false;
bool tid_till_600_lt8  = false;
bool hast_lt600  = false;
bool amot_data_ok  = false;
bool acc_f_eq0   = false;
bool lage_landst_reglage_ut  = false;
bool nodutf_ej_akt  = false;
bool hjulhast_lt15  = false;
bool hgen_ger_eff   = false;
// pla_lt_35gr = PLA < 35 GR
bool pla_lt_35gr   = false;
// tid_efter_lattn_gt1 = TID_EFTER_LATTN > 1
bool tid_efter_lattn_gt1   = false;
// adc_data_ok_ability_eq3 = ADC_DATA_OK * ABILITY = 3  
bool adc_data_ok_ability_eq3   = false;


// Larm calls

bool ll_larmorsak  = false;
bool hogfart	   = false;
bool intid	   = false;
bool uttid	   = false;
bool paminnelse	= false;
bool spak_hant  = false;

// FPL_TILLST

bool fpl_tillst_mark	 = false;
bool fpl_tillst_flygning = false;
bool fpl_tillst_domkraft = false;

// OUT parameters from this unit

bool fall_in_stall	    = false;
bool fall_ut_stall	    = false;
bool oppna_landst_luckor    = false;
bool stang_landst_luckor    = false;
bool oppna_avst_ventil	= false;

// TIME variables

bool maxtid_uppnad 		= false;
bool tid_efter_lattn_eq0 	= false;
bool tid_infallning_eq0         = false;
bool tid_infallning_lt3	        = false;
bool tid_infallning_gt20	= false;
bool tid_utfallning_eq0	        = false;
// tid_utfallning_lt5 = TID_UTFALLN < 5
bool tid_utfallning_lt5	= false;
// tid_utfallning_lt20 = TID_UTFALLN < 20
bool tid_utfallning_lt20 = false;
// tidut3_tidut2_lt3 = TID_UT3 - TID_UT2 < 3
bool tidut3_tidut2_lt3	= false;
bool lst_ut1_neq_lst_ut2 = false;
bool tidin3_eq_tid_infallning = false;
bool tidin2_eq_tid_infallning = false;
bool tidin1_eq_tid_infallning = false;

//
// Define all state variables with input from other units
//
void landstall_tillst ()
{
    alla_stall_inne = 
	(nosstall_inne1 || nosstall_inne2) &&
	(hstall_h_inne1 || hstall_h_inne2) &&
	(hstall_v_inne1 || hstall_v_inne2);
  
    alla_stall_ute =
	(nosstall_ute1 || nosstall_ute2) &&
	(hstall_h_ute1 || hstall_h_ute2) && 
	(hstall_v_ute1 || hstall_h_ute2);

    alla_stall_infj =
	(nosstall_infj1 || nosstall_infj2) &&
	(hstall_h_infj1 || hstall_h_infj2) &&
	(hstall_v_infj1 || hstall_v_infj2);
  
    alla_stall_utfj = 
	(!nosstall_infj1 || !nosstall_infj2) &&
	(!hstall_h_infj1 || !hstall_h_infj2) &&
	(!hstall_v_infj1 || !hstall_v_infj2);

    nosstall_utfj = 
	(nosstall_infj1 || nosstall_infj2);

    hstall_utfj = 
	(!hstall_h_infj1 || !hstall_h_infj2) &&
	(!hstall_v_infj1 || !hstall_v_infj2);

    hstall_infj =
	(hstall_h_infj1 || hstall_h_infj2) &&
	(hstall_v_infj1 || hstall_v_infj2);

    stallmanover_pagar =
	!alla_stall_inne || !alla_stall_ute;

    alla_luckor_stangda = 
	(nosstall_lucka_stangd1 || nosstall_lucka_stangd2) &&
	(hstall_h_lucka_stangd1 || hstall_h_lucka_stangd2) &&
	(hstall_v_lucka_stangd1 || hstall_v_lucka_stangd2);

    alla_luckor_oppna =
	(nosstall_lucka_oppen1 || nosstall_lucka_oppen2) &&
	(hstall_h_lucka_oppen1 || hstall_h_lucka_oppen2) &&
	(hstall_v_lucka_oppen1 || hstall_v_lucka_oppen2);

    luckmanover_pagar =
	!alla_luckor_stangda || !alla_luckor_oppna;

    if (!forsorjning_av_kritiska_blocket_ok) {
	alla_stall_utfj = 
	    !nosstall_infj2 && !hstall_h_infj2 && !hstall_v_infj2;
	hstall_utfj =
	    !hstall_h_infj2 && !hstall_v_infj2;
    }
}


//
// UTFALLNING_SEKVENS
//
void utfallning_sekvens ()
{
    if (alla_stall_ute) {
	if (alla_luckor_stangda) {
	    utfallning_pagar=false;
	}
	else {
	    oppna_landst_luckor=false;
	    stang_landst_luckor=true;
	    if (!tidut3_tidut2_lt3)
		utfallning_pagar=false;
	}
    }
    else {
	bool tmp1 = false;
	if (!alla_luckor_oppna) {
	    tmp1 = ((nosstall_lucka_stangd1 || nosstall_lucka_stangd2) ||
		    (hstall_h_lucka_stangd1 || hstall_h_lucka_stangd2) ||
		    (hstall_v_lucka_stangd1 || hstall_v_lucka_stangd2) ||
		    tid_utfallning_lt5);
	    if (tmp1) {
		oppna_avst_ventil=true;
		stang_landst_luckor=false;
		oppna_landst_luckor=true;
		fall_in_stall=true;
		fall_ut_stall=false;
	    }
	}
	if (!tmp1) {
	    fall_in_stall=false;
	    fall_ut_stall=true;
	}

	if (!tid_utfallning_lt20) {
	    maxtid_uppnad=true;
	}

	if (maxtid_uppnad) {
	    ll_larmorsak=true;
	    intid=true;
	    utfallning_pagar=false;
	}
    }
}

//
// UTFALLNING_LOV
//
void utfallning_lov ()
{
    if (adc_data_ok_ability_eq3) {
	if (hast_lt600) {
	    utfallning_tillaten=true;
	    utfallning_tillaten=false;
	}
    }
    else {
	utfallning_tillaten=true;
	if (amot_data_ok) {
	    if(pla_lt_35gr) {
		ll_larmorsak=true;
		paminnelse=true;
	    }
	}
    }
}

//
// INFALLNING_LOV
//
void infallning_lov ()
{
    if (alla_stall_utfj) {
	if (tid_efter_lattn_gt1) {
	    if (adc_data_ok_ability_eq3) {
		if(hast_lt600) {
		    if(tid_till_600_lt8) {
			ll_larmorsak=true;
			hogfart=true;
			infallning_tillaten=true;
		    }
		}
		else {
		    ll_larmorsak=true;
		    hogfart=true;
		    infallning_tillaten=false;
		}
	    }
	    else {
		infallning_tillaten=true;
	    }
	}
	else {
	    infallning_tillaten=false;
	}
    }
    else {
	tid_efter_lattn_eq0=true;
	infallning_tillaten=false;
	utfallning_tillaten=true;
    }
}
  
//
//    INFALLNING_SEKVENS
//

void infallning_sekvens ()
{
    if (alla_stall_inne) {
	if (alla_luckor_stangda) {
	    oppna_avst_ventil=false;
	    stang_landst_luckor=true;
	    fall_in_stall=false;
	    fall_ut_stall=false;
	    tid_infallning_eq0=true;
	    infallning_pagar=false;
	}
	else {
	    oppna_avst_ventil=true;
	    oppna_landst_luckor=false;
	    stang_landst_luckor=true;
	    tidin3_eq_tid_infallning=true;
	}
    }
    else {
	if(alla_luckor_oppna) {
	    fall_ut_stall=false;
	    fall_in_stall=true;
	    tidin2_eq_tid_infallning=true;
	}
	else {
	    oppna_avst_ventil=true;
	    stang_landst_luckor=false;
	    oppna_landst_luckor=true;
	    spin_down=true;
	    tidin1_eq_tid_infallning=true;
	}
    }
 
    if (!tid_infallning_lt3) {
	if (tid_infallning_gt20) {
	    ll_larmorsak=true;
	    intid=true;
	}
	else {
	    spin_down=false;
	}
    }
}

//
//   LUCKMANOVRERING_MARK
//
void luckmanovrering_mark ()
{
    oppna_avst_ventil=true;
    oppna_landst_luckor=false;
    stang_landst_luckor=true;

    if (alla_stall_infj) {
	if (hjulhast_lt15) {
	    if (!hgen_ger_eff) {
		stang_landst_luckor=false;
		oppna_landst_luckor=true;
	    }
	}
	else {
	    if (hgen_ger_eff) {
		oppna_landst_luckor=false;
		stang_landst_luckor=true;
	    }
	}
    }
    else {
	if (!fpl_tillst_domkraft) {
	    oppna_landst_luckor=false;
	    stang_landst_luckor=true;
	}
	else {
	    oppna_landst_luckor=true;
	    stang_landst_luckor=false;
	}
    }
}

//
// MANOVRERING
//
void manovrering ()
{
    if (utfallning_pagar) {
	utfallning_sekvens();
    }
    else {
	if (lage_landst_reglage_ut) {
	    if(lst_ut1_neq_lst_ut2) {
		landst_regl_fel=true;
	    }
	    spin_down=false;
	    infallning_pagar=false;
	    if (alla_stall_ute) {
		spak_hant_ok=true;
		luckmanovrering_mark();
	    }
	    else {
		if (!utfallning_tillaten)
		    spak_hant_ok=false;
		if (spak_hant_ok) {
		    if (maxtid_uppnad) {
			ll_larmorsak=true;
			uttid=true;
		    }
		    else {
			utfallning_pagar=true;
			tid_utfallning_eq0=true;
		    }
		}
		else {
		    ll_larmorsak=true;
		    spak_hant=true;
		}
	    }
	}
	else {
	    bool done=false;
	    
	    acc_f_eq0=true;
	    maxtid_uppnad=false;
	    tid_utfallning_eq0=true;
	    
	    if (fpl_tillst_mark) {
		oppna_avst_ventil=true;
		oppna_landst_luckor=true;
		fall_ut_stall=true;
	    }
	    if (!infallning_pagar) {
		if (alla_stall_inne) {
		    spak_hant_ok=true;
		}
		if (alla_stall_inne && alla_luckor_stangda) {
		    done=true;
		}
		if (!done && !infallning_tillaten)
		    spak_hant_ok=false;

		if (!done && !(spak_hant_ok && nodutf_ej_akt)) {
		    ll_larmorsak=true;
		    spak_hant=true;
		    done=true;
		}

		if (!done && fpl_tillst_domkraft) {
		    oppna_landst_luckor=false;
		    stang_landst_luckor=true;
		}

		if (!done && !fpl_tillst_flygning) {
		    if (!fpl_tillst_domkraft || !alla_luckor_stangda)
			done=true;
		}
		if (!done) {
		    spin_down=true;
		    infallning_pagar=true;
		    tid_infallning_eq0=true;
		}
	    }
	    else {
		if (!done)
		    infallning_sekvens();
	    }
	}
    }
}

//
// MANOVERINDIKERING (dummy)
//
void manoverindikering ()
{
}

//
// Main control program
//
void landstall ()
{
    landstall_tillst();

    if (utfallning_pagar) utfallning_sekvens();
    else if (alla_stall_inne) utfallning_lov();
    else if (alla_stall_ute)  infallning_lov();

    manovrering();
    manoverindikering();
}


