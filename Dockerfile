# Step 1: Base image with Ubuntu
FROM ubuntu:latest
# Step 2: Install OpenJDK 8 and Gradle
RUN apt-get update && \
    apt-get install -y openjdk-8-jdk && \
    apt-get install -y unzip wget && \
    apt-get clean
RUN apt-get update && apt-get install -y dos2unix && apt-get clean
RUN apt-get install -y git
# Download and install Gradle
ENV GRADLE_VERSION 6.9
RUN wget -q https://services.gradle.org/distributions/gradle-${GRADLE_VERSION}-bin.zip && \
    unzip -q gradle-${GRADLE_VERSION}-bin.zip -d /opt && \
    rm gradle-${GRADLE_VERSION}-bin.zip
ENV GRADLE_HOME=/opt/gradle-${GRADLE_VERSION}
ENV PATH=${GRADLE_HOME}/bin:${PATH}
# Step 3: Set the working directory
WORKDIR /app
# Step 4: Copy files from the current directory to the working directory
COPY . .
RUN dos2unix /app/entrypoint.sh && chmod +x /app/entrypoint.sh
# Step 5: Run a Bash script
CMD ["/bin/bash", "entrypoint.sh"]
