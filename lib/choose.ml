let choose (lst : 'a list) : 'a =
  let i = Random.int (List.length lst) in
  List.nth lst i

let choose_split (lst : 'a list) : 'a * ('a list) =
  let rec extract i lst =
    let hd = List.hd lst in
    if i == 0
    then (hd, List.tl lst)
    else let (a, lst') = extract (i - 1) (List.tl lst) in
         (a, hd :: lst') in
  extract (Random.int (List.length lst)) lst

let choose_frequency (freqs : (int * 'a) list) : 'a =
  let rec get_freq (freqs : (int * 'a) list) (i : int) : 'a =
    let (n, a) = List.hd freqs in
    if i < n
    then a
    else get_freq (List.tl freqs) (i - n) in

  let n = List.fold_left (fun acc (m, _) -> acc + m) 0 freqs in
  get_freq freqs (Random.int n)

let choose_frequency_split (freqs : (int * 'a) list) : 'a * ((int * 'a) list) =
  let rec extract_freq i lst =
    let hd = List.hd lst in
    if i < fst hd
    then (snd hd, List.tl lst)
    else let (a, lst') = extract_freq (i - fst hd) (List.tl lst) in
         (a, hd :: lst') in
  let n = List.fold_left (fun acc (m, _) -> acc + m) 0 freqs in
  extract_freq (Random.int n) freqs

