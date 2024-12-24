# FormalForward

- Add latte repo to workspace
- One thm one item for train, make common thm expicit?
- Add Digit type and prop like mul/add
- Add how to solve equation in latte
- Develop a inferce/result like proof
- Write a qucik sort in latte
- Proof QuickSort and BobbleSort equal.
- Convert LeanEucilid to latte
- Convert GSM8k/MATH/AIMO to latte
- Compare train w/o prompt "think in latte"
- Inference in MCTS.
- How to add inductive type and pattern match

## Set Up Dev Env
```shell
wget https://codeberg.org/leiningen/leiningen/raw/branch/stable/bin/lein
sudo mv lein /usr/local/bin
sudo chmod +x /usr/local/bin/lein
```

## How to Use Latte
```shell
cd latte/LATTE
lein repl
(latte.main/run-certify! "latte-integers" '[latte-integers.int])
```