# FormalForward

- One thm one item for train, make common thm expicit?
- After train, give some easy math to proof?
- Inference in MCTS.

- Add Digit type and prop like mul/add
- Add Real/limit logic
- Add how to solve equation in latte
- Develop a inferce/result like proof
- Write a qucik sort in latte
- Proof QuickSort and BobbleSort equal
- Convert text to latte
- Convert GSM8k/MATH/AIMO to latte
- Compare train w/o prompt "think in latte"
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

## Latte Repo
```shell
git clone https://github.com/latte-central/LaTTe.git
git clone https://github.com/latte-central/latte-kernel.git
git clone https://github.com/latte-central/latte-prelude.git
git clone https://github.com/latte-central/latte-sets.git
git clone https://github.com/latte-central/latte-integers.git
git clone https://github.com/latte-central/latte-nats.git
git clone https://github.com/latte-central/latte-finsets.git
git clone https://github.com/latte-central/latte-lists.git
```