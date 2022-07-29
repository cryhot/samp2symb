#!/usr/bin/env bash

BASHRC="$HOME"/.bashrc
RCSTART="# start (see '$(realpath "${BASH_SOURCE[0]}")')"
RCEND="# end (see '$(realpath "${BASH_SOURCE[0]}")')"
echo "$RCSTART" >> "$BASHRC"

# add this library to the path
export PYTHONPATH="$PYTHONPATH:$(realpath .)"  # configure current shell
echo 'export PYTHONPATH="$PYTHONPATH:'"$(realpath .)"'"' >> "$BASHRC"


sudo apt-get update
sudo apt-get install -y python3-pip libpython3-dev
python3 -m pip install --upgrade pip


# # install spot (according to https://spot.lrde.epita.fr/install.html#Debian)
# wget -q -O - https://www.lrde.epita.fr/repo/debian.gpg | sudo apt-key add -
# echo 'deb http://www.lrde.epita.fr/repo/debian/ stable/' | sudo tee -a /etc/apt/sources.list >/dev/null
# sudo apt-get update
# sudo apt-get install -y spot libspot-dev spot-doc python3-spot # Or a subset of those

# install clingo, etc (Answer Set Programming)
sudo apt-get install -y gringo
make -C samp2symb/algo/asp/


# install Rust (https://www.rust-lang.org/) (required by caqe)
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y
source "$HOME"/.cargo/env  # configure current shell (.bashrc already updated)

# installing caqe
sudo apt-get install -y cmake
pushd "$HOME"  # or any other directory
git clone https://github.com/ltentrup/caqe.git
cd caqe
git checkout 4.0.2  # or any other stable version
cargo build --release
export PATH="$PATH:$(realpath ./target/release)"  # configure current shell
echo 'export PATH="$PATH:'"$(realpath ./target/release)"'"' >> "$BASHRC"
popd

# dependency of ltlf2dfa python library
sudo apt-get install -y mona


# python libraries and wrappers
pip3 install -r requirements.txt

#TODO: spot


echo "$RCEND" >> "$BASHRC"