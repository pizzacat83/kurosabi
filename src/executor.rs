extern crate alloc;

use crate::{info, result::Result};
use alloc::boxed::Box;
use alloc::collections::vec_deque::VecDeque;
use core::{
    fmt,
    future::Future,
    panic::Location,
    pin::Pin,
    sync::atomic::{AtomicBool, Ordering},
    task::{Context, Poll},
};

pub fn demo() {
    let task1 = Task::new(async {
        for i in 100..=103 {
            info!("{i}");
            yield_execution().await;
        }
        Ok(())
    });
    let task2 = Task::new(async {
        for i in 200..=203 {
            info!("{i}");
            yield_execution().await;
        }
        Ok(())
    });

    let mut executor = Executor::new();
    executor.enqueue(task1);
    executor.enqueue(task2);
    Executor::run(executor);
}

struct Task<T> {
    future: Pin<Box<dyn Future<Output = Result<T>>>>,
    created_at_file: &'static str,
    created_at_line: u32,
}

impl<T> Task<T> {
    #[track_caller]
    fn new(future: impl Future<Output = Result<T>> + 'static) -> Task<T> {
        Task {
            future: Box::pin(future),
            created_at_file: Location::caller().file(),
            created_at_line: Location::caller().line(),
        }
    }

    fn poll(&mut self, context: &mut Context) -> Poll<Result<T>> {
        self.future.as_mut().poll(context)
    }
}

impl<T> fmt::Debug for Task<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Task({}:{})", self.created_at_file, self.created_at_line)
    }
}

struct Executor {
    task_queue: Option<VecDeque<Task<()>>>, // TODO: why option?
}

impl Executor {
    fn new() -> Self {
        Self { task_queue: None }
    }

    fn task_queue(&mut self) -> &mut VecDeque<Task<()>> {
        self.task_queue.get_or_insert_with(VecDeque::new)
    }

    fn enqueue(&mut self, task: Task<()>) {
        self.task_queue().push_back(task);
    }

    fn run(mut executor: Self) -> ! {
        info!("Executor starts running...");
        loop {
            let task = executor.task_queue().pop_front();
            if let Some(mut task) = task {
                let context = ();
                match task.poll(&mut context) {
                    Poll::Ready(v) => {
                        info!("Task completed: {task:?}: {v:?}")
                    }
                    Poll::Pending => {
                        info!("Still in progress: {task:?}");
                        executor.task_queue().push_back(task);
                    }
                }
            }
        }
    }
}

async fn yield_execution() {
    Yield::new().await
}

struct Yield {
    polled: AtomicBool,
}

impl Yield {
    fn new() -> Self {
        Self {
            polled: AtomicBool::new(false),
        }
    }
}

impl Future for Yield {
    type Output = ();

    fn poll(self: Pin<&mut Self>, _: &mut Context) -> Poll<Self::Output> {
        if self.polled.fetch_or(true, Ordering::SeqCst) {
            Poll::Ready(())
        } else {
            Poll::Pending
        }
    }
}
