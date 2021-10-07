# Install Docker itself if you don't have it already.

  * [Mac installer](https://docs.docker.com/v17.12/docker-for-mac/install/)

  * [Windows installer](https://docs.docker.com/v17.12/docker-for-windows/install/)

  * On linux:

```bash
sudo apt install docker.io
sudo service docker restart
sudo addgroup $USER docker
newgrp docker
```

# Pull the image.
(This is the slow thing; it includes a couple GB of Ubuntu.)

```bash
    docker pull jonhdotnet/summer_school:1.1
```

# Run the image

Run the image connected to your filesystem so you can edit in your OS, and then run Dafny from inside the docker container:

```bash
mkdir work
cd work
docker container run -t -i --mount src="`pwd`",target=/home/dafnyserver/work,type=bind --workdir /home/dafnyserver/work jonhdotnet/summer_school:1.1 /bin/bash
git clone https://github.com/GLaDOS-Michigan/summer-school-2021.git
cd summer-school-2021/chapter01-basics
```

Now you can edit files using your preferred native OS editor under the work/
directory, and verify them with Dafny from the terminal that's running the
docker image.

The docker-based command-line Dafny installation above is offered as a
portable, simple way to get started.  There do exist snazzy real-time Dafny
integrations for IDEs (Visual Studio, VSCode) and editors (Emacs, Vim).  You
are certainly welcome to install Dafny natively and integrate it with your
editor if you prefer.

