/*
 * Copyright (C) 2015, United States Government, as represented by the
 * Administrator of the National Aeronautics and Space Administration.
 * All rights reserved.
 *
 * Symbolic Pathfinder (jpf-symbc) is licensed under the Apache License, 
 * Version 2.0 (the "License"); you may not use this file except
 * in compliance with the License. You may obtain a copy of the License at
 * 
 *        http://www.apache.org/licenses/LICENSE-2.0. 
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and 
 * limitations under the License.
 */
package gov.nasa.jpf.symbc.tree.visualizer;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.text.SimpleDateFormat;
import java.util.Date;
import java.util.logging.Logger;

import org.apache.commons.lang.SystemUtils;

import att.grappa.Attribute;
import att.grappa.Graph;
import att.grappa.Node;

import gov.nasa.jpf.Config;
import gov.nasa.jpf.JPF;
import gov.nasa.jpf.symbc.tree.NodeFactory;

/**
 * @author Kasper Luckow
 */
public class DOTVisualizerListener extends AVisualizerListener<Node> {

  private static final Logger logger = JPF.getLogger(DOTVisualizerListener.class.getName());
  
  private enum OUTPUT_FORMAT {
    DOT("dot"),
    PNG("png"),
    EPS("eps"),
    PDF("pdf"),
    PS("ps"),
    SVG("svg");

    private String format;

    OUTPUT_FORMAT(String format) {
      this.format = format;
    }

    public String getFormat() {
      return this.format;
    }
  }

  protected Graph graph;

  private final static String OUTPUT_FORMAT_CONF = "symbolic.visualizer.outputformat";
  private final static String OUTPUT_PATH = "symbolic.visualizer.outputpath";
  private final OUTPUT_FORMAT format;
  private final String basePath;
  
  public DOTVisualizerListener(Config conf, JPF jpf) {
    super(conf, jpf);
    String outputFormat = conf.getString(OUTPUT_FORMAT_CONF, "dot");
    this.format = OUTPUT_FORMAT.valueOf(outputFormat.toUpperCase());
    basePath = conf.getString(OUTPUT_PATH, "./");
  }

  @Override
  protected NodeFactory<Node> getNodeFactory() {
    graph = new Graph("Graph");
    return new DOTFactory(graph);
  }

  @Override
  protected void processTree() {
    SimpleDateFormat form = new SimpleDateFormat("ddMMyy-hhmmss");
    String filename = super.targetMethod.substring(super.targetMethod.lastIndexOf('.') + 1);
    filename += "_" + form.format(new Date()) + ".dot";
    String filepath = new File(basePath, filename).getAbsolutePath();
    outputVisualization(filepath);
    logger.info("Wrote DOT file of symbolic method: " + super.targetMethod + " to " + filepath);
  }

  private void outputVisualization(String path) {
    File file = new File(path); 
    try {
      FileOutputStream fo = new FileOutputStream(file);
      graph.printGraph(fo);
      fo.close();
    } catch (FileNotFoundException e) {
      e.printStackTrace();
    } catch (IOException e) {
      e.printStackTrace();
    }

    if(format != OUTPUT_FORMAT.DOT) {
      if((SystemUtils.IS_OS_LINUX ||
          SystemUtils.IS_OS_MAC_OSX ||
          SystemUtils.IS_OS_MAC)) {
        try {
          convertDotFile(file, format);
          file.delete();
        } catch (InterruptedException e) {
          e.printStackTrace();
        }
      }
    }
  }

  private void convertDotFile(File file, OUTPUT_FORMAT format) throws InterruptedException {
    String dotCmd = "dot " + file.getPath() + " -T" + format.getFormat() + " -o " + file.getPath().replace(".dot", "." + format.getFormat());
    try {
      Process p = Runtime.getRuntime().exec(dotCmd);
      p.waitFor();
      p.exitValue();
      p.destroy();
    } catch (IOException e) {
      e.printStackTrace();
    }
  }
}
