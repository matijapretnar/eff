open OcamlHeader;;let rec _loop_pure_42 _x_48 = 
                     if coer_arrow coer_refl_ty coer_refl_ty (( = ) _x_48) 0 then () else 
                     _loop_pure_42 
                       (coer_arrow coer_refl_ty coer_refl_ty (( - ) _x_48) 1)  

;; let loop_pure = _loop_pure_42
;;
let _test_pure_49 = fun (_n_50: int) -> _loop_pure_42 _n_50 

;; let test_pure = _test_pure_49
;;
type(_, _) eff_internal_effect += Fail : (unit, empty) eff_internal_effect 
;;
let rec _loop_latent_51 _x_62 = 
      coer_computation coer_refl_ty 
        (coer_return coer_refl_ty 
           (coer_arrow coer_refl_ty coer_refl_ty (( = ) _x_62))) >>= (fun 
         _b_54 -> coer_computation coer_refl_ty 
                    (coer_return coer_refl_ty (_b_54 0)) >>= (fun  _b_53 -> coer_computation coer_refl_ty 
                                                                    (coer_computation coer_refl_ty 
                                                                    (if _b_53 then 
                                                                    coer_return coer_refl_ty 
                                                                    () else 
                                                                    coer_computation coer_refl_ty 
                                                                    (coer_return coer_refl_ty 
                                                                    (coer_arrow coer_refl_ty coer_refl_ty 
                                                                    (( < ) 
                                                                    _x_62))) >>= (fun 
                                                                     _b_56 -> coer_computation coer_refl_ty 
                                                                    (coer_return coer_refl_ty 
                                                                    (_b_56 0)) >>= (fun 
                                                                     _b_55 -> coer_computation coer_refl_ty 
                                                                    (coer_computation coer_refl_ty 
                                                                    (if _b_55 then 
                                                                     Call (Fail, (), (fun 
                                                                    (_y_64: empty) -> coer_computation coer_refl_ty 
                                                                    (coer_return coer_refl_ty 
                                                                    (match _y_64 with
                                                                     _ -> assert false)))) else 
                                                                    coer_computation coer_refl_ty 
                                                                    (coer_return coer_refl_ty 
                                                                    (coer_arrow coer_refl_ty coer_refl_ty 
                                                                    (( - ) 
                                                                    _x_62))) >>= (fun 
                                                                     _b_59 -> coer_computation coer_refl_ty 
                                                                    (coer_return coer_refl_ty 
                                                                    (_b_59 1)) >>= (fun 
                                                                     _b_58 -> coer_computation coer_refl_ty 
                                                                    (coer_computation coer_refl_ty 
                                                                    (coer_computation coer_refl_ty 
                                                                    (_loop_latent_51 
                                                                    _b_58))))) )))) )))) 

;; let loop_latent = _loop_latent_51
;;
let _test_latent_66 = 
     fun (_n_67: int) -> coer_computation coer_refl_ty 
                           (_loop_latent_51 _n_67) 

;; let test_latent = _test_latent_66
;;
type(_, _) eff_internal_effect += Incr : (unit, unit) eff_internal_effect 
;;
let rec _loop_incr_68 _x_76 = 
      coer_computation coer_refl_ty 
        (coer_return coer_refl_ty 
           (coer_arrow coer_refl_ty coer_refl_ty (( = ) _x_76))) >>= (fun 
         _b_71 -> coer_computation coer_refl_ty 
                    (coer_return coer_refl_ty (_b_71 0)) >>= (fun  _b_70 -> coer_computation coer_refl_ty 
                                                                    (coer_computation coer_refl_ty 
                                                                    (if _b_70 then 
                                                                    coer_return coer_refl_ty 
                                                                    () else 
                                                                     Call (Incr, (), (fun 
                                                                    (_y_78: unit) -> coer_computation coer_refl_ty 
                                                                    (coer_computation coer_refl_ty 
                                                                    (coer_return coer_refl_ty 
                                                                    (coer_arrow coer_refl_ty coer_refl_ty 
                                                                    (( - ) 
                                                                    _x_76)))) >>= (fun  _b_73 -> coer_computation coer_refl_ty 
                                                                    (coer_computation coer_refl_ty 
                                                                    (coer_return coer_refl_ty 
                                                                    (_b_73 1))) >>= (fun  _b_72 -> coer_computation coer_refl_ty 
                                                                    (coer_computation coer_refl_ty 
                                                                    (coer_computation coer_refl_ty 
                                                                    (coer_computation coer_refl_ty 
                                                                    (_loop_incr_68 
                                                                    _b_72)))))))) )))) 

;; let loop_incr = _loop_incr_68
;;
let _test_incr_79 = 
     fun (_n_80: int) -> coer_arrow coer_refl_ty coer_refl_ty 
                           (coer_arrow coer_refl_ty coer_refl_ty 
                              (let rec _loop_incr_108 (_x_76, _k_110) = 
                                  if coer_arrow coer_refl_ty coer_refl_ty 
                                       (( = ) _x_76) 0 then _k_110 () else 
                                  coer_arrow coer_refl_ty coer_refl_ty 
                                    (fun (_x_240: int) -> coer_arrow coer_refl_ty coer_refl_ty 
                                                            (coer_arrow coer_refl_ty coer_refl_ty 
                                                               (_loop_incr_108 
                                                                  (coer_arrow coer_refl_ty coer_refl_ty 
                                                                    (( - ) 
                                                                    _x_76) 1, (
                                                                   fun 
                                                                    (_x_246: unit) -> _k_110 
                                                                    _x_246)))) 
                                                            (coer_arrow coer_refl_ty coer_refl_ty 
                                                               (( + ) _x_240) 
                                                               1))  
                               in 
                               _loop_incr_108 
                                 (_n_80, (fun (_x_251: unit) -> coer_arrow coer_refl_ty coer_refl_ty 
                                                                  (fun 
                                                                    (_x_89: int) -> _x_89))))) 
                           0 

;; let test_incr = _test_incr_79
;;
let rec _loop_incr'_252 _x_260 = 
      coer_computation coer_refl_ty 
        (coer_return coer_refl_ty 
           (coer_arrow coer_refl_ty coer_refl_ty (( = ) _x_260))) >>= (fun 
         _b_255 -> coer_computation coer_refl_ty 
                     (coer_return coer_refl_ty (_b_255 0)) >>= (fun  _b_254 -> coer_computation coer_refl_ty 
                                                                    (coer_computation coer_refl_ty 
                                                                    (if _b_254 then 
                                                                    coer_return coer_refl_ty 
                                                                    () else 
                                                                    coer_computation coer_refl_ty 
                                                                    (coer_computation coer_refl_ty 
                                                                    (coer_return coer_refl_ty 
                                                                    (coer_arrow coer_refl_ty coer_refl_ty 
                                                                    (( - ) 
                                                                    _x_260)))) >>= (fun 
                                                                     _b_257 -> coer_computation coer_refl_ty 
                                                                    (coer_computation coer_refl_ty 
                                                                    (coer_return coer_refl_ty 
                                                                    (_b_257 1))) >>= (fun 
                                                                     _b_256 -> coer_computation coer_refl_ty 
                                                                    (coer_computation coer_refl_ty 
                                                                    (coer_computation coer_refl_ty 
                                                                    (coer_computation coer_refl_ty 
                                                                    (_loop_incr'_252 
                                                                    _b_256)))) >>= (fun 
                                                                     _ ->  Call (Incr, (), (fun 
                                                                    (_y_262: unit) -> coer_computation coer_refl_ty 
                                                                    (coer_computation coer_refl_ty 
                                                                    (coer_computation coer_refl_ty 
                                                                    (coer_return coer_refl_ty 
                                                                    _y_262)))))))) )))) 

;; let loop_incr' = _loop_incr'_252
;;
let _test_incr'_263 = 
     fun (_n_264: int) -> coer_arrow coer_refl_ty coer_refl_ty 
                            (coer_arrow coer_refl_ty coer_refl_ty 
                               (let rec _loop_incr'_517 (_x_260, _k_520) = 
                                   if coer_arrow coer_refl_ty coer_refl_ty 
                                        (( = ) _x_260) 0 then _k_520 () else 
                                   _loop_incr'_517 
                                     (coer_arrow coer_refl_ty coer_refl_ty 
                                        (( - ) _x_260) 1, (fun (_x_704: unit) -> coer_arrow coer_refl_ty coer_refl_ty 
                                                                    (fun 
                                                                    (_x_705: int) -> coer_arrow coer_refl_ty coer_refl_ty 
                                                                    (coer_arrow coer_refl_ty coer_refl_ty 
                                                                    (_k_520 
                                                                    ())) 
                                                                    (coer_arrow coer_refl_ty coer_refl_ty 
                                                                    (( + ) 
                                                                    _x_705) 1))))  
                                and _loop_incr_518 (_x_76, _k_710) = 
                                   if coer_arrow coer_refl_ty coer_refl_ty 
                                        (( = ) _x_76) 0 then _k_710 () else 
                                   coer_arrow coer_refl_ty coer_refl_ty 
                                     (fun (_x_840: int) -> coer_arrow coer_refl_ty coer_refl_ty 
                                                             (coer_arrow coer_refl_ty coer_refl_ty 
                                                                (_loop_incr_518 
                                                                   (coer_arrow coer_refl_ty coer_refl_ty 
                                                                    (( - ) 
                                                                    _x_76) 1, (
                                                                    fun 
                                                                    (_x_846: unit) -> _k_710 
                                                                    _x_846)))) 
                                                             (coer_arrow coer_refl_ty coer_refl_ty 
                                                                (( + ) _x_840) 
                                                                1)) in 
                                _loop_incr'_517 
                                  (_n_264, (fun (_x_851: unit) -> coer_arrow coer_refl_ty coer_refl_ty 
                                                                    (
                                                                    fun 
                                                                    (_x_273: int) -> _x_273))))) 
                            0 

;; let test_incr' = _test_incr'_263
;;
type(_, _) eff_internal_effect += Get : (unit, int) eff_internal_effect 
;;
type(_, _) eff_internal_effect += Put : (int, unit) eff_internal_effect 
;;
let rec _loop_state_852 _x_865 = 
      coer_computation coer_refl_ty 
        (coer_return coer_refl_ty 
           (coer_arrow coer_refl_ty coer_refl_ty (( = ) _x_865))) >>= (fun 
         _b_855 -> coer_computation coer_refl_ty 
                     (coer_return coer_refl_ty (_b_855 0)) >>= (fun  _b_854 -> coer_computation coer_refl_ty 
                                                                    (coer_computation coer_refl_ty 
                                                                    (if _b_854 then 
                                                                    coer_return coer_refl_ty 
                                                                    () else 
                                                                     Call (Get, (), (fun 
                                                                    (_y_869: int) -> coer_computation coer_refl_ty 
                                                                    (coer_computation coer_refl_ty 
                                                                    (coer_computation coer_refl_ty 
                                                                    (coer_computation coer_refl_ty 
                                                                    (coer_return coer_refl_ty 
                                                                    (coer_arrow coer_refl_ty coer_refl_ty 
                                                                    (( + ) 
                                                                    _y_869)))))) >>= (fun 
                                                                     _b_857 -> coer_computation coer_refl_ty 
                                                                    (coer_computation coer_refl_ty 
                                                                    (coer_computation coer_refl_ty 
                                                                    (coer_return coer_refl_ty 
                                                                    (_b_857 1)))) >>= (fun 
                                                                     _b_856 ->  Call (Put, _b_856, (fun 
                                                                    (_y_867: unit) -> coer_computation coer_refl_ty 
                                                                    (coer_computation coer_refl_ty 
                                                                    (coer_return coer_refl_ty 
                                                                    (coer_arrow coer_refl_ty coer_refl_ty 
                                                                    (( - ) 
                                                                    _x_865)))) >>= (fun  _b_860 -> coer_computation coer_refl_ty 
                                                                    (coer_computation coer_refl_ty 
                                                                    (coer_return coer_refl_ty 
                                                                    (_b_860 1))) >>= (fun  _b_859 -> coer_computation coer_refl_ty 
                                                                    (coer_computation coer_refl_ty 
                                                                    (coer_computation coer_refl_ty 
                                                                    (coer_computation coer_refl_ty 
                                                                    (_loop_state_852 
                                                                    _b_859)))))))))))) )))) 

;; let loop_state = _loop_state_852
;;
let _test_state_871 = 
     fun (_n_872: int) -> coer_arrow coer_refl_ty coer_refl_ty 
                            (coer_arrow coer_refl_ty coer_refl_ty 
                               (let rec _loop_state_902 (_x_865, _k_904) = 
                                   if coer_arrow coer_refl_ty coer_refl_ty 
                                        (( = ) _x_865) 0 then _k_904 () else 
                                   coer_arrow coer_refl_ty coer_refl_ty 
                                     (fun (_s_1119: int) -> coer_arrow coer_refl_ty coer_refl_ty 
                                                              (coer_arrow coer_refl_ty coer_refl_ty 
                                                                 (coer_arrow coer_refl_ty coer_refl_ty 
                                                                    (
                                                                    fun 
                                                                    (_: int) -> coer_arrow coer_refl_ty coer_refl_ty 
                                                                    (coer_arrow coer_refl_ty coer_refl_ty 
                                                                    (_loop_state_902 
                                                                    (coer_arrow coer_refl_ty coer_refl_ty 
                                                                    (( - ) 
                                                                    _x_865) 1, (
                                                                    fun 
                                                                    (_x_1125: unit) -> _k_904 
                                                                    _x_1125)))) 
                                                                    (coer_arrow coer_refl_ty coer_refl_ty 
                                                                    (( + ) 
                                                                    _s_1119) 
                                                                    1)))) 
                                                              _s_1119)  
                                in 
                                _loop_state_902 
                                  (_n_872, (fun (_x_1130: unit) -> coer_arrow coer_refl_ty coer_refl_ty 
                                                                    (fun 
                                                                    (_x_882: int) -> _x_882))))) 
                            0 

;; let test_state = _test_state_871
;;
