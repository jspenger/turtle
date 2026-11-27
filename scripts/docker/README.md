# Docker

## How to build

Building the docker image takes up to 2 hours using up to 11 GB of RAM.

```bash
docker build -f scripts/docker/Dockerfile -t turtle .
```

## How to run

```bash
docker run --rm -it turtle
```
