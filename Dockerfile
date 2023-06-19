FROM openjdk:8u312-jdk

# Install Git
RUN apt-get update && apt-get install -y git

# Set the working directory
WORKDIR /app

# Install Gradle
ENV GRADLE_VERSION 6.9
ENV GRADLE_HOME /opt/gradle
ENV PATH $PATH:$GRADLE_HOME/bin

RUN wget -q "https://services.gradle.org/distributions/gradle-${GRADLE_VERSION}-bin.zip" -O /tmp/gradle.zip \
    && unzip -q /tmp/gradle.zip -d /opt \
    && mv "/opt/gradle-${GRADLE_VERSION}" "$GRADLE_HOME" \
    && rm /tmp/gradle.zip

# Clone the Git repository
RUN git clone --recurse-submodules https://github.com/gaurangkudale/SPF.git -b SPF .

# Add any additional setup or configuration steps here

# Run multiple commands using a shell script
COPY entrypoint.sh /app/entrypoint.sh
RUN chmod +x /app/entrypoint.sh
CMD ["/app/entrypoint.sh"]
