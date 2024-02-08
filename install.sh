set -ve

# Install basic packages
apt-get update
apt-get install -y --no-install-recommends bison flex

# Install GMP library
wget https://gmplib.org/download/gmp/gmp-6.3.0.tar.xz
tar -xvf gmp-6.3.0.tar.xz
cd gmp-6.3.0
./configure --with-pic
make
make install
cd ..
python3.7 -m pip install gmpy2


# Install PBC library
wget https://crypto.stanford.edu/pbc/files/pbc-0.5.14.tar.gz
tar -xvzf pbc-0.5.14.tar.gz
cd pbc-0.5.14
./configure
make
make install
cd ..

# Install OpenSSL library
wget https://www.openssl.org/source/openssl-3.2.0.tar.gz
tar -xvzf openssl-3.2.0.tar.gz
cd openssl-3.2.0
./Configure
make
make install
cd ..

# Install Charm library
git clone https://github.com/JHUISI/charm.git
cd charm
git checkout 6ac1d445fa0bd81b880c1a83accd8791acd2594b
./configure.sh
make
make install
cd ..