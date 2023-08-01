#!/usr/bin/env bash
# run this code to install the library on a fresh virtual machine
# this script is highly invasive, is is recommended to install manually on personnal devices

REPO="$(dirname "$(realpath "${BASH_SOURCE[0]}")")"
BASHRC="$HOME"/.bashrc
RCSTART="# start (see '$(realpath "${BASH_SOURCE[0]}")')"
RCEND="# end (see '$(realpath "${BASH_SOURCE[0]}")')"
echo "$RCSTART" >> "$BASHRC"

# add this library to the path
pushd "$REPO"
export PYTHONPATH="$PYTHONPATH:$(realpath .)"  # configure current shell
echo 'export PYTHONPATH="$PYTHONPATH:'"$(realpath .)"'"' >> "$BASHRC"
popd


sudo apt-get update
# sudo apt-get upgrade -y  # make sure all packages are up to date
sudo apt-get install -y python3-pip libpython3-dev
python3 -m pip install --upgrade pip


# # install spot (according to https://spot.lrde.epita.fr/install.html#Debian)
# wget -q -O - https://www.lrde.epita.fr/repo/debian.gpg | sudo apt-key add -
# echo 'deb http://www.lrde.epita.fr/repo/debian/ stable/' | sudo tee -a /etc/apt/sources.list >/dev/null
# sudo apt-get update
# sudo apt-get install -y spot libspot-dev spot-doc python3-spot # Or a subset of those

# install spot (according to https://spot.lre.epita.fr/install.html#tar)
pushd "$HOME"  # or any other directory (just for sources)
wget http://www.lrde.epita.fr/dload/spot/spot-2.11.3.tar.gz -O spot-2.11.3.tar.gz
tar xzvf spot-2.11.3.tar.gz
#rm spot-2.11.3.tar.gz
cd spot-2.11.3/
./configure
make
prefix="$(make -qp | sed -n "s/^prefix[ ]*=[ ]*//g p")"  # get python version
for d in $(find "$prefix/lib/" -type d -name dist-packages); do
    pushd "$d/.."
    #sudo rmdir site-packages
    sudo ln -s dist-packages site-packages
    popd
done
sudo make install
sudo ldconfig
popd

# install clingo, etc (Answer Set Programming)
sudo apt-get install -y gringo
pushd "$REPO"
make -C samp2symb/algo/asp/
popd


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
pushd "$REPO"
pip3 install -r requirements.txt
popd



echo "$RCEND" >> "$BASHRC"