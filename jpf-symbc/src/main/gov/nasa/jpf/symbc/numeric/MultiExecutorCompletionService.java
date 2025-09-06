package gov.nasa.jpf.symbc.numeric;

import java.util.concurrent.*;

/**
 * A simple completion service that works across multiple executors.
 * Tasks are submitted to different executors, but their completed
 * results are collected in a single blocking queue. This allows
 * retrieving results in the order tasks finish, regardless of
 * which executor ran them.
 */
public class MultiExecutorCompletionService<V> {
    private final BlockingQueue<Future<V>> completionQueue = new LinkedBlockingQueue<>();

    /**
     * Submits a task to the given executor and adds its Future
     * to the completion queue once it finishes.
     *
     * @param executor the executor to run the task
     * @param task     the callable task
     * @return a Future representing the submitted task
     */
    public Future<V> submit(ExecutorService executor, Callable<V> task) {
        FutureTask<V> futureTask = new FutureTask<V>(task) {
            @Override
            protected void done() {
                completionQueue.add(this);
            }
        };
        executor.submit(futureTask);
        return futureTask;
    }

    /**
     * Retrieves and removes the next completed task's Future,
     * waiting if necessary until one is available.
     *
     * @return the next completed Future
     * @throws InterruptedException if interrupted while waiting
     */
    public Future<V> take() throws InterruptedException {
        return completionQueue.take();
    }
}
