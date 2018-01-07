# Script that does setup for artifact, and calls the experiments.

set -ex
cd $(dirname $0)

# Configurable.
CVC4=/usr/local/bin/cvc4

# Check everything exists.
python -c "import yaml" || {
  echo "Installing yaml."
  sudo apt-get install python-yaml
} && echo "YAML already found or installed."

python -c "import pyparsing" || {
  echo "Installing pyparsing"
  sudo apt-get install python-pyparsing
} && echo "pyparsing already found or installed."


[ -f  $CVC4 ] || {
  echo "Downloading CVC4."
  sudo wget -q 'http://cvc4.cs.stanford.edu/downloads/builds/x86_64-linux-opt/cvc4-1.5-x86_64-linux-opt' -O $CVC4
  sudo chmod u+x $CVC4
} && echo "CVC4 already found or installed."

cd ../test
sudo ./runall.py
